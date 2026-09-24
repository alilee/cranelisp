# design/int/

Interior design for the **Binary / integration layer** — `src/` +
`crates/cranelisp-exe-bundle/`. Canonical bounded context:
`design/arch/bounded-contexts.md` §6. Maintained by `design` (int).

## Ownership — orchestration and host-client, not the runtime library

`/int` is the integration/application layer: it wires the other surfaces into a
deployable artefact and a working REPL. It owns:

- the three **internal cadences** (compilation, REPL, watcher) and their handoffs;
- the **scheduler + worker subsystem** and the compiler-internal concurrency
  (dependency service, signature/body pre-pass, mutual-import cycle handling) —
  the *compiler-internal* scheduling axis, **distinct** from the language-level
  effect-concurrency runtime;
- REPL session, slash-command dispatch, prompt/display, introspection (REPL-only, D1/D1b);
- module-loading orchestration, cache writer, save/regenerate, file watcher;
- macro execution + the Pass-1 expand loop; CLI parsing; the exe-bundle startup stub;
- platform-DLL **load orchestration** (`load_platform_dll`, `/platform-schema`) and the
  `ABI_VERSION` loader gate; observability ring buffers (`io_trace`/`scheduler_trace`/`got_trace`).

**`/int` is a host-CLIENT of the IO/RC runtime library, not its owner.** How IO is managed at
run time — the reactor, async trampoline, `consume_io_tree`, permit pools, RC/drop discipline,
lifetime-across-suspension — is a runtime-library implementation detail encapsulated in
**`cranelisp-intrinsics`** (`design/intrinsics/reactor.md`), which `cranelisp-backend` emits
calls into (`design/arch/bounded-contexts.md` §4b). `/int`'s only contact with that runtime is the **thin host-client seam**
(`design/intrinsics/reactor.md` §0): it drives IO through the single C-ABI entry `cranelisp_run_io` for `--run`/REPL
and propagates the loader ABI refusal. Reactor construction and execution remain
inside intrinsics. It never reaches into reactor internals.
`bind-chain-analysis.md` — the *compile-time* IO-scheduling pass — is int's: it is a
pipeline transform, while execution of the nodes it emits is the runtime library's.

## Document index

This memory establishes two Binary/int-owned collections. Neither is a
historical-reference exemption: a live reference in either must resolve.

| Collection | Purpose |
|---|---|
| `int-current-designs` | The master, subsystem and active feature designs for pipeline orchestration, compiler-internal scheduling, REPL/session, persistence, macro execution, host integration and observability. |
| `int-reference-lineage` | Retained race-analysis, defect-wave and migration records that live source or tests still cite as a contract of record or a diagnosis anchor. They are evidence, not current design intent. |

When a subordinate doc, a lineage record and the current source disagree, the
**source and the master win**.

**Master.** `int.md` — the single source of design intent for the binary
surface; every other doc is subordinate.

**Current entry point.** `s122-closure.md` — the selected S122 Binary/int
closure and the continuous Phase-5 source reservation. Open Binary/int
obligations are listed in `int.md` §16.0 and the standing review rejects in
`int.md` §12.1.

### Subsystem designs

| Doc | Subject |
|---|---|
| `concurrency-architecture.md` | The compiler-internal scheduling axis: where int is concurrent, why, and which doc carries each invariant. |
| `persistent-workers.md` | The delivered worker-lifecycle contract — spawn, park/wake, enqueue-not-spawn, per-batch JIT, shutdown. Section numbers are pinned by live source. |
| `signature-body-prepass.md` | The S93 two-phase barrier — the durable race cure. |
| `session-transaction.md` | Live redefinition: the guarded-publication model, commit-gate slot classification (including trait-implementation redefinition, §2.5), slot versioning, the retention pool and persistence. Section numbers are pinned by live source; it also marks the superseded dependent-recompilation residue. |
| `session-persistence.md`, `cache-hit-loading.md` | Save/regenerate and cache-hit module loading; `cache-hit-loading.md` §0 is the restoration-parity rule. The cache artefact, cache-hit flow and `Code` carrier are `int.md` §§5 and 7. |
| `io-integration.md` | Host-side IO forcing and platform-DLL load wiring. |
| `result-owner.md` | The one program-result owner across REPL, `--run`, cache-hit and linked startup: observe, then release exactly once through canonical type glue. |
| `macro-turn-ownership.md` | The macro-clause invocation protocol: the declared all-Owned clause ABI, single-owner argument transfer by ABI crossing, and exactly-once result discharge through `consume_sexp`. |
| `bind-chain-analysis.md` | The compile-time automatic-IO-scheduling pass (`spec/10-io.md` §10.12), including how it reads a platform function's scheduling class (`design/int/bind-chain-analysis.md` §4). |
| `observability.md` | The trace and event sinks. |
| `macro-resolver-impl.md`, `cranelisp-toml.md`, `repl-lifecycle.md` | Macro resolution, project configuration, REPL lifecycle and project-root resolution. |
| `agent.md` | The embedded agent (dispatch, turn loop, harvest, write gates, rendering, log and trace), `/refs`, `/tests-for`, `/syntax` and the interim `/search` index. Section numbers are pinned by live source. |
| `terminal-styling.md` | The layered styling interior below the `styled::render` role-span seam, and the pretty-printer layout. |
| `concurrency/` | As-built structural, protocol and lifecycle diagrams for the scheduling axis. |

### Active feature designs

| Doc | Subject |
|---|---|
| `s117-conformance-recovery.md` | The prepared-turn transaction (prepare → whole-batch codegen → publish, one cadence for eval and worker), its presentation readers, and the source-ordered macro checkpoint (§1.1.2/§2.1). |
| `index-worker-isolation.md` | The index-feed isolation contract (background half; the foreground export-closure gate is `int.md` §6.7). |
| `macro-diagnostic-reanchoring.md` | Synthetic-span diagnostics over macro output relocate to the origin form; paired with `design/frontend/binder-head-reject.md`. |
| `expansion-qualification-scope.md` | `qualify_expanded_sexp` is scope-aware, skipping value-level binder slots. |
| `multi-sig-introspection.md` | Multi-signature introspection, with the D1 constraint-display read-follow (§2.4). |
| `private-submodule-import.md` | Private submodule imports. |

### Reference lineage

| Doc | Why retained |
|---|---|
| `heisenbug-race-closure.md` | The S61 per-interleaving treadmill. Precedent for race-class investigation and the rationale for live instruments; `index-worker-isolation.md` and `signature-body-prepass.md` cite it. Section numbers are pinned by live source. |
| `s102-defect-wave.md` | The S102 Block-A defect-wave cluster designs. Cited section-precisely by live source and tests. |
| `step9-error-cascade.md` | The failure/cascade design; §4.1 and §4.2 are cited by spec-traced tests. |
| `cache-prelude-restoration-repro.md` | The diagnosis anchor `tests/cache.rs` names. |

Landed-migration and superseded-slice records were deleted during the S122
consolidation; Git retains them, and their substance lives in `int.md`.

## Cross-references

- `design/arch/bounded-contexts.md` §6 — canonical int bounded context (cadences, handoffs, constraints).
- `design/intrinsics/reactor.md` — the IO/RC runtime library `/int` is a host-client of (§0 = the seam).
- `design/intrinsics/CLAUDE.md` — the runtime-library ownership statement (the callee side).
- `design/arch/effect-concurrency.md` — the arch-owned language-level concurrency model (distinct from int's compiler-internal scheduler).
