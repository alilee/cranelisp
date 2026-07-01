---
number: 0419
target: /arch
filed_by: /arch
filed_at: 2026-06-20
sprint_filed: 87
refers_to: src/platform.rs:231 (JIT/REPL HostCallbacks construction), crates/cranelisp-exe-bundle/src/lib.rs:131-144 (--link startup-stub construction + the "this makes the --link path match" comment), src/platform/tests.rs:157-158 (test mirror wired_host_callbacks), crates/cranelisp-platform/src/lib.rs (HostCallbacks contract + alloc rustdoc), crates/cranelisp-intrinsics/src/alloc.rs (heap_alloc_payload + cranelisp_alloc_with_tag)
status: open
resolution: home decided by /arch (S98); implementation owed to /dev
---

# Shared consumer-side `HostCallbacks` builder — DEF-6 divergence-proofing (standalone Principle-7 dedup)

## /arch ruling (S98, 2026-07-01) — home + surface DECIDED; implementation owed to /dev

With FIXME 0407 **retired by design** (the platform-effect boundary is poll-in/wake-out
only — no closure-callback capability, `effect-concurrency.md` §12.1; `HostCallbacks`
will never be widened with `invoke_closure`/`rc_inc`/`rc_dec`), 0419's "0407
prerequisite" role is **gone**. It collapses to a **standalone Principle-7 dedup**: the
`HostCallbacks` table is hand-constructed at two mirrored production sites plus one test
mirror, the DEF-6 heap-corruption window.

**HOME: `cranelisp-intrinsics`.** **SURFACE: one public free function**

```rust
// crates/cranelisp-intrinsics/src/…  (e.g. alloc.rs or a small host_callbacks module)
/// The canonical host-callbacks table handed to every platform manifest call.
/// Single source of truth for the intrinsic function pointers a platform DLL
/// receives — DEF-6 divergence-proofing: one builder, every mode calls it, so the
/// `alloc` = payload-returning vs base-returning mismatch cannot recur by hand-mirror.
pub fn host_callbacks() -> cranelisp_platform::HostCallbacks {
    cranelisp_platform::HostCallbacks {
        alloc: crate::alloc::heap_alloc_payload,
        alloc_with_tag: crate::alloc::cranelisp_alloc_with_tag,
    }
}
```

**Crate-DAG reasoning (Principle 3 — dependency flows toward stability).**

- `HostCallbacks` is defined in `cranelisp-platform`; its two fields are function
  pointers OWNED by `cranelisp-intrinsics` (`heap_alloc_payload`,
  `cranelisp_alloc_with_tag`). A builder that names **both** the struct and both
  pointers must live in a crate that can name both.
- `cranelisp-platform` **correctly cannot** host it — it must NOT depend on
  `cranelisp-intrinsics` (that inverts the DAG, Principle 3). Platform stays the
  dependency-clean contract *definition*; it never names the intrinsic pointers.
- `cranelisp-intrinsics` **already depends on `cranelisp-platform`** (so it can name
  `HostCallbacks`) and **owns** both function pointers — so it is the **lowest** crate
  that can name both. The DAG is respected: no new edge, no inversion.
- A host-side `fn host_callbacks()` in `src/` was considered and **rejected**: the two
  production consumers are in **two different crates** — the binary (`src/platform.rs`)
  and `cranelisp-exe-bundle` — and `exe-bundle` is a *dependency of* the binary, not the
  reverse, so it cannot call a function in `src/`. The only home both consumers (and the
  test mirror) can reach is a crate **below both** in the DAG: `cranelisp-intrinsics`.
  Both sites already call `cranelisp_intrinsics::heap_alloc_payload` directly today, so
  the new dependency edge is zero (already present).

**Public-API impact.** `cranelisp-intrinsics` gains ONE new `pub fn host_callbacks() ->
cranelisp_platform::HostCallbacks`. That is a new line on the intrinsics
`public-api.txt` baseline; the /dev implementer regenerates it in the same change-set
(baseline-diff discipline). `cranelisp-types` is untouched — `HostCallbacks` already
exists in `cranelisp-platform`; this is a construction-site consolidation, not a
boundary-type change. `cranelisp-platform` is unchanged (it stays the contract
definition).

**Implementation owed to /dev (band-E task).** Replace the three hand-built literals with
`cranelisp_intrinsics::host_callbacks()`:
`src/platform.rs:231` (JIT/REPL), `crates/cranelisp-exe-bundle/src/lib.rs:131` (`--link`
startup stub — deleting the 10-line "this makes the `--link` path match" cross-file
comment, whose reason for existing dissolves), and the test mirror
`src/platform/tests.rs:157` (`wired_host_callbacks` delegates to the one builder). Add a
`cranelisp-intrinsics` unit test pinning `host_callbacks().alloc == heap_alloc_payload`
(the payload-vs-base invariant DEF-6 violated). **Leave this FIXME OPEN until /dev lands
the consolidation.**

## Scope confirmation (S94, /arch — reactor construction is OUT)

/design int's S94 Phase-3 finding: the **reactor** `HostCtx`/`Waker` construction is
**already divergence-proof by construction** — `make_host_ctx` is single-sited in
`cranelisp-intrinsics` (`reactor.rs`) and reached by ALL modes through the one C-ABI
entry `cranelisp_run_io` (which lives in intrinsics and links into `--link` output).
There is no second hand-mirrored site to diverge from, so it carries no DEF-6 hazard.

**Ruling:** 0419 stays **narrowly the platform-DLL `HostCallbacks` consolidation** —
the two hand-mirrored sites `src/platform.rs:253` + `crates/cranelisp-exe-bundle/src/lib.rs:131`
(+ the test mirror). **Reactor / `HostCtx` construction is explicitly OUT of 0419's
scope** — do NOT fold it into the shared builder; over-generalizing the sound,
single-sited reactor path would manufacture coupling where none exists (the opposite
of this FIXME's intent). S94 leaves the reactor construction exactly as /design int
built it. 0419 remains off the S94 critical path (only the `--run`/REPL
host-construction site is active this sprint; `--link` concurrency is a later slice).

## Issue

The S87 Stage-B audit confirmed, from **both** consumer crates (src/ F-B +
platform F2), the JIT-vs-`--link` host-callback divergence the S86 charter named.
The runtime `HostCallbacks` value is hand-constructed at **two production sites in
two crates with no shared builder**:

- `src/platform.rs:253` — `--run` / REPL / JIT (`load_platform_dll`).
- `crates/cranelisp-exe-bundle/src/lib.rs:131` — `--link` startup stub
  (`cranelisp_init_platform`).

The two sites now **agree** — but only by **manual mirroring + a 10-line
cross-file comment** (`exe-bundle/src/lib.rs:132-141`: "the JIT path already wires
`heap_alloc_payload`; this makes the `--link` path match"). That comment is the
tell: the contract is documented prose pointing at a sibling file, not a single
construction both modes call. **DEF-6 was exactly the window where they did NOT
match** (one wired `heap_alloc` = base-returning, the other `heap_alloc_payload` =
payload-returning — a heap-corrupting mismatch) and nothing structural prevented
it. This is the Principle-7 (single source of truth) / Principle-8 (mode
divergence) anti-pattern `memory/feedback_review_root_cause_and_duplication` warns
about.

The platform crate **correctly cannot** fix it (it must not depend on
`cranelisp-intrinsics` — that would invert the DAG, Principle 3). The platform's
own **layout-hash export path is the divergence-proof counter-example** (platform
§3.3: one data representation, both modes dereference identically) — the shape the
callback wiring should adopt.

## Proposed resolution

Introduce ONE shared consumer-side `HostCallbacks` builder in the lowest crate that
can name both intrinsic pointers (`cranelisp-intrinsics`, or a host-side
`fn host_callbacks() -> HostCallbacks` both `src/platform.rs` and
`cranelisp-exe-bundle` call). Both production sites + the test mirror
(`src/platform.rs:932`) call it. The platform crate stays unchanged (it is the
correct, dependency-clean contract definition). This makes the contract
divergence-proof-by-construction rather than divergence-prone-by-hand-mirror.

`/arch` decides the builder's home + ABI surface; `/dev` int + `/dev` backend
implement.

## Operational implication / Context

- **Stage-B backlog item B3 (theme T3).** Synthesis answer to chartered question
  (b) (`audits/s87-findings.md §4-b`): the shared builder IS the right fix and IS
  truly the 0407 prerequisite.
- **~~0407 prerequisite~~ — RETIRED (S98).** FIXME 0407 (Model-B closure callbacks)
  is retired by design (`effect-concurrency.md` §12.1): the platform-effect boundary
  is poll-in/wake-out only, and `HostCallbacks` will NEVER gain
  `invoke_closure`/`rc_inc`/`rc_dec`. The "sequencing condition" is therefore void —
  0419 no longer gates a 3-field widening. It stands as a **standalone Principle-7
  dedup** (DEF-6 divergence-proofing), in band-E scope for S98.
- **Phase-H gate disposition: N/A.** With 0407 retired, the conditional gate-in
  ("iff 0407 is scheduled within the Phase-H arc") is moot. 0419 is scheduled directly
  in S98 band E — /arch sets the home (this fire); /dev lands the consolidation.
- When actioned, this is the natural co-resolution point for the standing fork-join
  error-slot ferry obligation at the callback boundary (cross-ref
  `design/arch/test-discovery.md`; platform F6 confirms the platform half is sound,
  the join-side propagation is the open half).
