---
number: 0337
target: /arch
filed_by: /sprint
filed_at: 2026-06-13
sprint_filed: 81
refers_to: design/arch/fixmes/0327-arch-fault-guarded-dispatch-funnel-boundary.md (STEP-4 FINDING), design/arch/bounded-contexts.md §4b invariant 14 + §5 invariant 9, crates/cranelisp-platform/src/lib.rs (CLIO::effect / call_effect_thunk), crates/cranelisp-intrinsics/src/io_guard.rs, platforms/boom (repro fixture), tests/platform_errors.rs::platform_dispatch_error_carries_fn_name (ignored repro)
status: open    # RULED by /arch S81 (Option A); closes when the fix lands + the boom repro goes green
ruled_at: 2026-06-13
recorded_in: design/arch/bounded-contexts.md §5 invariant 9 (the DLL-local-catch sub-ruling, canonical) + §4b invariant 14 (intrinsics reads the cross-ABI signal, drops the panic catch_unwind) + §3 (backend bake/stamp UNTOUCHED)
implementing_skills: /platform (DLL-local catch in CLIO::effect* + EffectOutcome #[repr(C)] + call_effect_thunk return contract + ABI 4→5 + platform baseline regen) → /dev int-on-intrinsics (force_effect_thunk_protected reads EffectOutcome, drops panic catch_unwind, keeps sigsetjmp) → /qa (un-ignore tests/platform_errors.rs::platform_dispatch_error_carries_fn_name)
---

# Dispatch-funnel fault catch must be DLL-local — host `catch_unwind` cannot cross the cdylib panic-runtime boundary

## /arch ruling (S81, 2026-06-13) — Option A (DLL-local catch + cross-C-ABI fault signal); Option B rejected as-built

**Decision: Option A.** The fault catch must execute **inside the DLL**, by the DLL's own
panic runtime, and the caught fault must cross the C-ABI back to the host **as a value**.

**Decisive rationale (Option B is infeasible as-built).** A platform `cdylib` statically
links its **own** copy of the Rust panic runtime (`rust_begin_unwind` / `rust_eh_personality`
DLL-local, `nm`-confirmed). The faulting closure body lives inside the DLL (`CLIO::effect` is
monomorphised at the DLL's `crash()` call site; the `Box<dyn FnOnce>` vtable points into DLL
code), so a `panic!` at force time unwinds with the **DLL's** runtime. `extern "C-unwind"`
(Option B) only flips the *abort-at-FFI-boundary default* into *unwind-may-propagate* — it
does **NOT** let the host's `catch_unwind` catch an unwind begun by a *different* Rust
runtime. A DLL-originated unwind reaching the host `catch_unwind` is still UB/abort under
`C-unwind`. So B is neither necessary nor sufficient for the cross-cdylib panic, and it would
pull the whole `call_effect_thunk` chain onto a more constraining ABI for no gain. The catch
must happen on the DLL side of the runtime boundary → Option A.

**The DLL-local catch site:** `cranelisp_platform::CLIO::effect[_on_resource]`'s thunk
wrapper — the one frame that is (a) monomorphised into every DLL that uses it and (b) owns the
user closure. The wrapper runs the user closure under a DLL-local `catch_unwind`; `Ok(v)` →
return the value; `Err(payload)` → record the panic-cause string and signal the host across
the C-ABI. No backend wrapper is needed — the W-G backend bake/stamp is untouched.

**The cross-C-ABI fault-signal shape (the TLS-across-boundary resolution).** The DLL links its
own `cranelisp-platform` (its own thread-locals) and CANNOT set the host intrinsics
dispatch-fault slot directly — so the fault travels as a **C-ABI return value**, never TLS.
`call_effect_thunk` changes its return contract from bare `i64` to a `#[repr(C)]`:

```
#[repr(C)]   // layout-contract type; NO #[non_exhaustive]; governed by ABI_VERSION (Principle 14)
pub struct EffectOutcome {
    pub value: i64,             // the thunk result when clean
    pub fault_cause: *const u8, // null = clean; non-null = DLL-owned panic-cause UTF-8 bytes
    pub fault_len: usize,       // length of fault_cause when non-null
}
```

Null `fault_cause` → clean, `value` is the result. Non-null → faulted; `fault_cause` points at
DLL-owned UTF-8 bytes (leaked for the session, bounded by §5 invariant 6 "no DLL unloading
mid-session", mirroring the existing `declare_platform!` `Box::leak`s); `value` is unused. This
new type lives in **`cranelisp-platform`** (it is a platform-ABI `#[repr(C)]` type, NOT a
cross-crate DTO → it does **not** go in `cranelisp-types`). The DLL's `CLIO::effect` wrapper
produces the `fault_cause` half from the caught payload; the host's `call_effect_thunk` copy
merely *forwards* the struct (it does **no** `catch_unwind` of its own). `/dev` adds this
`cranelisp-platform` type when implementing — `/arch` does not add it now (design-only pass).

**Host trampoline shrinks to reading the signal.** `io_guard::force_effect_thunk_protected`
**drops its panic-side `catch_unwind`** (nothing host-side to catch) and reads `EffectOutcome`:
clean → `ForceOutcome::Value(value)`; faulted → compose `DispatchFault { fn_name (field-3, read
host-side as today), cause (the DLL C-string) }` onto the dispatch-fault slot, return
`ForceOutcome::Faulted`. Int's `DispatchError` compose is unchanged.

**Hard-fault (signal) half — disposition.** KEEP the host-side `sigsetjmp`/signal handler. A
genuine hardware trap from foreign **C** code is process-global (delivered to the faulting
thread regardless of which cdylib raised it), so the host handler catches it across the DLL
boundary once reached — it is not subject to the panic-runtime-boundary problem. The Rust
null-deref subtlety resolves cleanly under Option A: rustc emits a null-deref as a
*non-unwinding panic*, which the DLL-local `catch_unwind` now catches on the **panic** path (not
the signal path); genuine C-level memory faults still take the signal path. Both converge on the
same `DispatchFault` slot. Implementer flag: assert the panic fault in the `boom` fixture, and —
if cheap — add a C-level SIGSEGV sibling fault to exercise the signal half across the boundary.

**ABI bump: YES — `ABI_VERSION` 4→5.** The `call_effect_thunk` force-return contract + the new
`EffectOutcome` layout are a host↔DLL layout-contract change (Principle 14): a v4 DLL must be
rejected against a v5 host (the force-return shape differs), so the gate must bump. The
`IO_TAG_EFFECT` node layout (the v3→4 field-3 widen) is **unchanged** — the bump is purely the
force-return contract. Platform `public-api.txt` regenerates (the `EffectOutcome` type +
`call_effect_thunk` signature + `ABI_VERSION` lines).

**Owning crate:** `cranelisp-platform` owns the DLL-local catch (the `CLIO::effect*` wrapper),
the `EffectOutcome` type, the `call_effect_thunk` return-contract change, and the `ABI_VERSION`
bump. `cranelisp-intrinsics` shrinks (drops the panic `catch_unwind`, keeps the signal half,
reads `EffectOutcome`). `cranelisp-types` UNCHANGED. `cranelisp-backend` UNCHANGED.

**Implementing-skills sequence:**
1. **/platform** — DLL-local `catch_unwind` in `CLIO::effect[_on_resource]` + `EffectOutcome`
   `#[repr(C)]` + `call_effect_thunk` returns `EffectOutcome` + `ABI_VERSION` 4→5 + platform
   `public-api.txt` regen.
2. **/dev (int)** on `cranelisp-intrinsics` — `force_effect_thunk_protected` reads
   `EffectOutcome` (remove the panic-side `catch_unwind`; retain the `sigsetjmp` signal half),
   composes `DispatchFault`. Int's `DispatchError` compose unchanged.
3. **/qa** — un-ignore `tests/platform_errors.rs::platform_dispatch_error_carries_fn_name`
   (FIXME 0289 item 5 → green; the lone suite skip retires).

**Cross-reference.** FIXME 0327 stays OPEN (its STEP-4 FINDING is the same gap; it closes when
the funnel lands end-to-end). This FIXME (0337) stays OPEN and closes when the Option-A fix
lands + the `boom` repro goes green.

## RESIDUAL fn-name GAP (S81 W-Closer, 2026-06-13, /qa) — Option-A abort half LANDED; fault-path fn-name still `<unknown>`

The Option-A implementation (`9fb89ed`) **fixed the process-abort half** — verified by the un-ignored
e2e and a standalone `--run` repro. The boom dispatch fault now:

- **does NOT abort** — exit **1** (clean structured error), NOT abort **134** (foreign-exception abort
  is gone; the DLL-local `catch_unwind` + `EffectOutcome` cross-C-ABI signal works), and
- carries the **correct cause string**: `boom: deliberate dispatch-time fault in platform fn `crash``,
- surfaces as a structured `PlatformError::DispatchError` (`platform fn `…` dispatch failed: …`).

**BUT the baked FQ fn-name is `<unknown>` on the fault path.** The surfaced error reads
`user.cl:1:1: error: platform fn `<unknown>` dispatch failed: boom: …` — NOT
`platform fn `platform.boom/crash` …`. So the e2e's third assertion (the `platform.boom/crash`
fn-name) fails; the first two (non-zero exit, `dispatch` carrier) pass.

**Diagnosis.** The backend stamps field-3 (the baked fn-name handle) into the returned Effect node
**AFTER** `call_effect_thunk` returns (the post-call stamp, ruling 0327 §2). On the **fault** path the
thunk panics, the DLL-local catch returns an `EffectOutcome` fault signal **instead of** a normal node,
and the post-call field-3 stamp never reaches a usable node — so the trampoline's field-3 read finds
null and degrades to `fn_name: "<unknown>"`. The clean path stamps field-3 fine (no fault); only the
faulting dispatch loses its name.

**Fix shape (resolver: /backend + /platform; NOT /qa).** The fn-name must travel on a
**fault-path-independent channel**: either stamp field-3 **before** the force (so it survives a panic),
or carry the baked name in the `EffectOutcome` / a side channel the trampoline reads on the faulted
branch, so the host has the name regardless of whether the thunk faulted. The `cause` already crosses
correctly via `EffectOutcome.fault_cause`; the fn-name needs the same fault-surviving treatment.

**Repro (committed, durable).** `platforms/boom` + `tests/platform_errors.rs::platform_dispatch_error_carries_fn_name`,
which carries the as-built `<unknown>`-vs-`platform.boom/crash` assertion and is `#[ignore]`'d with this
residual-gap reason (un-ignore the moment the fn-name baking lands on the fault path). Standalone repro:
`CRANELISP_PLATFORM_PATH=target/debug cranelisp --run user.cl` for a program importing `platform.boom/crash`
and calling it → exit 1, `platform fn `<unknown>` dispatch failed: boom: …`.

This FIXME (0337) stays OPEN (closing condition narrows from "abort fixed" to "fault-path fn-name lands").
FIXME 0327 stays OPEN. FIXME 0289 item 5 stays OPEN. The lone suite skip remains (1277/0/1 after the
ABI-5 literal fix).

---

# (original finding below)

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
