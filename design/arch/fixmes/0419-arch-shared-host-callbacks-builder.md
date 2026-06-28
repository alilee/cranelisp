---
number: 0419
target: /arch
filed_by: /arch
filed_at: 2026-06-20
sprint_filed: 87
refers_to: src/platform.rs:253 (JIT/REPL HostCallbacks construction), crates/cranelisp-exe-bundle/src/lib.rs:131-141 (--link startup-stub construction + the "this makes the --link path match" comment), crates/cranelisp-platform/src/lib.rs:444-473 (HostCallbacks contract + alloc rustdoc), audits/cranelisp-platform-s87.md §3+F2, audits/src-s87.md F-B+§4, design/arch/fixmes/0407-platform-closure-callback-model-b.md
status: open
---

# Shared consumer-side `HostCallbacks` builder — DEF-6 root-enabler closure + 0407 prerequisite

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
- **0407 prerequisite (the sequencing condition).** FIXME 0407 (Model-B closure
  callbacks) widens `HostCallbacks` by 3 fields (`rc_inc`/`rc_dec`/`invoke_closure`)
  — multiplying the 2-site hand-mirror hazard by 3. **Do NOT widen `HostCallbacks`
  for 0407 before this builder lands.** 0407 stays open and cited (not actioned).
- **Phase-H gate disposition: MAYBE — conditional.** Gate-in B3 **iff** 0407 is
  scheduled within the Phase-H arc; otherwise it is deferrable consolidation
  (bucket ii). The gate (user) decides; this FIXME tracks the work either way.
- When actioned, this is the natural co-resolution point for the standing fork-join
  error-slot ferry obligation at the callback boundary (cross-ref
  `design/arch/test-discovery.md`; platform F6 confirms the platform half is sound,
  the join-side propagation is the open half).
