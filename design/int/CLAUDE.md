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
(`design/intrinsics/reactor.md` §0): it constructs the reactor once through the single C-ABI entry
`cranelisp_run_io`, drives `block_on_reactor` for `--run`/REPL, propagates the loader ABI
refusal, and reads the optional `/strand` dev sink. It never reaches into reactor internals.
`bind-chain-analysis.md` — the *compile-time* IO-scheduling pass — stays here; its finer
ownership is the open question in FIXME 0486.

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
| `session-transaction.md` | Live redefinition: the guarded-publication model, commit-gate slot classification, slot versioning, the retention pool and persistence. Section numbers are pinned by live source; it also marks the superseded dependent-recompilation residue. |
| `session-persistence.md`, `symbol-table-cache.md`, `cache-hit-loading.md` | Save/regenerate, the cached symbol table, and cache-hit module loading; `cache-hit-loading.md` §0 is the restoration-parity rule. |
| `io-integration.md` | Host-side IO forcing and platform-DLL load wiring. |
| `bind-chain-analysis.md` | The compile-time automatic-IO-scheduling pass (`spec/10-io.md` §10.12), including how it reads a platform function's scheduling class (`design/int/bind-chain-analysis.md` §4). |
| `observability.md` | The trace and event sinks. |
| `macro-resolver-impl.md`, `cranelisp-toml.md`, `repl-lifecycle.md` | Macro resolution, project configuration, REPL lifecycle and project-root resolution. |
| `agent.md` | The embedded-agent and `/search` index design — large and active. |
| `terminal-styling.md` | The `styled::render` role-span seam. |
| `concurrency/` | As-built structural, protocol and lifecycle diagrams for the scheduling axis. |

### Active feature designs

| Doc | Subject |
|---|---|
| `s117-conformance-recovery.md` | The prepared-turn transaction (prepare → whole-batch codegen → publish, one cadence for eval and worker), its presentation readers, and the source-ordered macro checkpoint (§1.1.2/§2.1). |
| `macro-turn-ownership.md` | The delivered macro-turn ownership protocol: single-owner marshalling, transfer by ABI crossing, exactly-once discharge through `consume_sexp`, the `MacroClauseAbi` declaration. |
| `result-owner.md` | The one program-result owner across REPL / `--run` / cache-hit / linked startup — observe-then-release, exact-once, type-directed. |
| `index-worker-isolation.md` | The index-feed isolation contract (background half). |
| `prelude-table-write-isolation.md` | The foreground public-write chokepoint, including candidate-batch validation before table or GOT publication (foreground half). |
| `quote-shield.md` | `expand_scoped` holds quoted data out of Pass-1 macro expansion. |
| `macro-diagnostic-reanchoring.md` | Synthetic-span diagnostics over macro output relocate to the origin form; paired with `design/frontend/binder-head-reject.md`. |
| `expansion-qualification-scope.md` | `qualify_expanded_sexp` is scope-aware, skipping value-level binder slots. |
| `impl-redefinition-hot-reload.md` | A same-type re-impl hot-reloads through the existing `commit_staging_to_live` → `commit_slotted_def` GOT-patch path; no impl-specific parallel path. |
| `multi-sig-introspection.md` | Multi-signature introspection, with the D1 constraint-display read-follow (§2.4). |
| `macro-marshal-rc-protection.md` | The 0638 diagnosis and its negative-control-twin argument. **§2's mechanism is superseded by `macro-turn-ownership.md` Rule 2** — read it as evidence, not as current mechanism. |
| `private-submodule-import.md`, `symbol-table-generics.md` | Private submodule imports; generics in the session symbol table. |

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
