---
number: 0327
target: /arch
filed_by: /design (platform)
filed_at: 2026-06-13
sprint_filed: 81
refers_to: design/platform/platform.md §9a, crates/cranelisp-intrinsics/src/io.rs:192, crates/cranelisp-platform/src/lib.rs:679 §707, crates/cranelisp-types/src/error.rs:261, src/expander.rs:494, design/arch/fixmes/0289-qa-platform-interface-e2e-walks.md (item 5), design/arch/bounded-contexts.md §4b §5 §6
status: open    # RULED by /arch S81 (implementation-ready); closes when the funnel lands
ruled_at: 2026-06-13
implementing_skills: /platform (node-widen + ABI 3→4 + fixture), /backend (bake + post-call stamp), /dev int (trampoline guard in intrinsics + DispatchError compose), /qa (un-ignore 0289-item-5)
recorded_in: design/arch/bounded-contexts.md §5 invariant 9 (canonical) + §4b invariant 14 (intrinsics half) + §3 (backend bake bullet); design/platform/platform.md §9a (platform /design home)
---

# Ratify the fault-guarded FFI-dispatch funnel boundary — guard placement + fn-name plumbing + DispatchError construction path

## /arch ruling (S81, 2026-06-13) — IMPLEMENTATION-READY (FIXME stays OPEN, closes when the funnel lands)

The /design (platform) recommendation is **RATIFIED with one factual correction**. The
canonical ruling is **BC §5 invariant 9** (rewritten this pass — the prior Phase-2
"zero public-surface delta, ride the `scheduling_class` channel" reading was WRONG and is
superseded; see below); BC §4b invariant 14 records the intrinsics half; BC §3 records the
backend bake. Coordinates:

1. **Guard placement — CONFIRMED.** The fault guard wraps the `call_effect_thunk`
   invocation in the **intrinsics IO trampoline** (`io.rs:192`), not `call_effect_thunk`
   and not each platform fn. `call_effect_thunk` stays a thin reclaim primitive in
   `cranelisp-platform`. Grounds: Principle 7 (single force site), Principle 6 (one guard).

2. **fn-name plumbing — Option A CONFIRMED; ABI 3→4 ACCEPTED.** The `IO_TAG_EFFECT` node
   widens to a **fourth `i64` field** (24→32 bytes) carrying a baked fn-name handle.
   **Factual correction to the /design proposal:** the proposal said the name is "stamped at
   the dispatch arm into the Effect node it builds." But the Effect node is built **inside
   the DLL** (`CLIO::effect_on_resource`, `lib.rs:679-697`), which the backend cannot reach.
   The corrected shape: (a) the DLL's `CLIO::effect*` **reserves** the field (allocates 32
   bytes, inits field-3 to null); (b) the backend bakes the statically-known fn-name at the
   GOT-indirect `DefKind::PlatformEffect` arm (same data-symbol family as the trace
   `DisplayDescriptor` baker) and emits IR that **stamps the baked pointer into the returned
   node's field-3 AFTER the platform-fn call returns**. A node the backend did not stamp (or
   an out-of-tree DLL building nodes itself) degrades to a null name → `fn_name: "<unknown>"`,
   not a crash. **Option B (thread-local at the dispatch arm) is REJECTED** — stale under
   Bind/Par deferred force (the as-built `io.rs:189` `scheduling_class: 0` placeholder is the
   exact same gap). **Why the prior "zero-delta / scheduling_class channel" reading was
   wrong:** `scheduling_class` is read at the *call site* in int (`bind_chain_analysis.rs`)
   BEFORE the IO tree is built — it never reaches the trampoline (hence the `0` placeholder).
   There is no call-site→trampoline channel; the name must travel WITH the node. ABI bump
   `ABI_VERSION` 3→4 (cheap pre-1.0) is the cost, ACCEPTED.

3. **Two-layer construction — CONFIRMED.** Intrinsics guard captures the fault
   (signal/panic/slot via `take_runtime_error()`) + the field-3 fn-name and returns an
   intrinsics-internal fault outcome (NOT a `PlatformError` — intrinsics is diagnostics-free
   by charter). **int composes `PlatformError::DispatchError { fn_name, cause, location }`** at
   its runtime-error surface (mirrors `invoke_jit_protected`: intrinsics sets the slot, int
   reads + composes), surfacing via `CranelispError::Platform`.

4. **Public-surface deltas.** `cranelisp-platform`: node-widen + `CLIO::effect*` + `ABI_VERSION`
   3→4 (baseline regen). `cranelisp-intrinsics`: possibly a fault-outcome carrier (internal by
   default; baseline-visible only if it must cross to int as a named type). `cranelisp-types`:
   **UNCHANGED** (`DispatchError` already exists) — CONFIRMED. `cranelisp-backend`: codegen-
   internal bake, no public-surface delta expected.

5. **Cross-component sequence:** (1) /platform node-widen + ABI 3→4 + fixture (regen platform
   baseline) → (2) /backend bake + post-call stamp → (3) /dev int trampoline guard (in
   intrinsics) + compose `DispatchError` → (4) /qa un-ignore 0289-item-5. **Regen-coordination
   flag:** sequence the backend dispatch-arm change with the **0325 backend baseline regen** so
   the backend `public-api.txt` is regenerated ONCE, not in two uncoordinated commits.

The funnel is implementation-ready for the S81 platform/backend/int/qa waves. This FIXME stays
OPEN and closes when the funnel lands (the e2e in FIXME 0289 item 5 goes green).

## STEP-4 FINDING (S81 W-G, 2026-06-13) — FIXME STAYS OPEN; a STEP-3 mechanism gap remains

Steps 1–3 landed (`aeff79d` / `d1949fb` / `f0d25dc`): node-widen + ABI 4, backend bake +
post-call stamp into field-3, and the intrinsics trampoline guard
(`force_effect_thunk_protected`) + int `DispatchError` compose. The step-4 e2e
(`/platform` fault test-DLL `platforms/boom` + `/qa` e2e
`tests/platform_errors.rs::platform_dispatch_error_carries_fn_name`) was authored and the
fixture built/wired into the canonical run. **But the e2e does NOT go green — it ABORTS the
process — because of a gap the io_guard unit tests could not catch:**

**The Rust-panic capture half of the guard does not cover a panic raised inside a
separately-compiled, dlopen'd platform cdylib.** The guard wraps the thunk force in the host's
`std::panic::catch_unwind`. The io_guard unit tests
(`force_effect_thunk_protected_rust_panic_is_caught`, …) create the panicking thunk **in the
host crate**, so panic-and-catch share ONE Rust runtime and `catch_unwind` works. A real
platform DLL is a `cdylib` that statically links its **own** copy of the Rust panic runtime —
`nm libcranelisp_boom.so` shows `rust_begin_unwind` / `rust_panic` / `rust_eh_personality`
defined LOCALLY in the `.so`. A `panic!` raised inside the DLL uses the DLL's runtime; when it
unwinds across the dlopen boundary into the host's `catch_unwind`, the host sees a FOREIGN
exception and the process aborts:

```
thread '<unnamed>' panicked at platforms/boom/src/lib.rs:…:
boom: deliberate dispatch-time fault in platform fn `crash`
fatal runtime error: Rust cannot catch foreign exceptions, aborting   (exit 134)
```

The signal-trap half (sigsetjmp/SIGSEGV/FPE/ILL/BUS) is unaffected by this and would still
capture genuine hardware traps from C code — but a Rust-level null-deref does NOT reach it
either (modern rustc emits a non-unwinding-panic null check that aborts before any SIGSEGV).

**Step-3 fix shape (next sprint — /platform + /backend, NOT step-4 e2e scope):** catch the
panic INSIDE the DLL, where the DLL's own runtime can catch it, and convert it to a
slot-set + sentinel BEFORE returning across the FFI boundary. Candidate sites:
`cranelisp_platform::CLIO::effect[_on_resource]` wraps the user thunk body in a DLL-local
`catch_unwind` + `set_runtime_error` (so the panic never crosses the boundary as an
exception), and/or the thunk-invocation ABI (`call_effect_thunk` / the thunk fn-pointer type)
moves to `extern "C-unwind"` so the unwind is permitted to cross. The host-side `catch_unwind`
+ sigsetjmp guard then catches the converted fault as designed. The field-3 fn-name plumbing,
backend bake, and int compose are all correct and need no change — only the panic must be made
catchable across the cdylib boundary.

**Minimal repro committed:** `platforms/boom` (the fault fixture) + the IGNORED
`tests/platform_errors.rs::platform_dispatch_error_carries_fn_name` (asserts the real as-built
`DispatchError { fn_name: "platform.boom/crash" }` shape; un-ignore the moment the step-3 fix
lands). FIXME 0289 item 5 stays open (fixture built, e2e wired-but-ignored, gap named here).

**/arch RULED this gap S81 (2026-06-13) — see FIXME 0337.** Mechanism: **Option A (DLL-local
`catch_unwind` in `cranelisp_platform::CLIO::effect*` + a `#[repr(C)] EffectOutcome` cross-C-ABI
fault signal returned by `call_effect_thunk`; `ABI_VERSION` 4→5)**. Option B (`extern "C-unwind"`)
rejected — it cannot make a panic begun in the DLL's runtime catchable by the host's
`catch_unwind` (two distinct cdylib panic runtimes). The intrinsics trampoline guard drops its
panic-side `catch_unwind` and reads `EffectOutcome` instead; the `sigsetjmp` signal half stays
(process-global signals cross the boundary). Backend bake/stamp untouched. Canonical: BC §5
invariant 9 (DLL-local-catch sub-ruling) + §4b invariant 14 + §3. Sequence: /platform →
/dev(int)-on-intrinsics → /qa. Both 0327 and 0337 stay OPEN until the funnel lands green.

**S81 W-F (arch-docs ratification) verification, 2026-06-13.** The W-F pass confirmed the BC
recording of this ruling is complete and self-consistent — the W-G implementer can build against
it with no further arch round-trip. Verified present and correct: **BC §5 invariant 9** (the full
ruling — guard placement, node-widen Option A with the DLL-reserves-field-3 / backend-stamps-post-call
factual correction, the scheduling_class-channel-is-wrong correction, two-layer `DispatchError`
construction, public-surface deltas, cross-component sequence, 0325 regen-coordination); **BC §4b
invariant 14** (the intrinsics half — guard at `io.rs:192`, captures fault + field-3 name, returns
an intrinsics-internal fault outcome, int composes); **BC §3** the platform-dispatch-fn-name-bake
bullet (backend bakes at the `DefKind::PlatformEffect` arm, same data-symbol family as the trace
`DisplayDescriptor` baker, post-call stamp into field-3, ABI 3→4); **BC §6** carries int's platform
load path and the `DispatchError` compose is the runtime-error-surface obligation named in §5 inv 9
+ §4b inv 14. No under-recording found; nothing added this pass. FIXME left OPEN (closes when the
funnel lands in W-G / FIXME 0289 item 5 goes green).

---

## Original /design (platform) recommendation (preserved below)

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
