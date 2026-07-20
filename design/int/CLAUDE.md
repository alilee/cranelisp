# design/int/

Interior design for the **Binary / integration layer** — `src/` + `crates/cranelisp-exe-bundle/`.
Canonical bounded context: `design/arch/bounded-contexts.md` §6.

## Ownership — orchestration + host-client, NOT the runtime library

`/int` is the **integration/application layer**: it wires the other surfaces into a
deployable artefact and a working REPL. It owns:

- the three **internal cadences** (compilation, REPL, watcher) and their handoffs;
- the **scheduler + worker subsystem** and the compiler-internal concurrency (dependency
  service, signature/body pre-pass, mutual-import cycle handling) — this is the
  *compiler-internal* scheduling axis, **distinct** from the language-level effect-concurrency
  runtime;
- REPL session, slash-command dispatch, prompt/display, introspection (REPL-only, D1/D1b);
- module-loading orchestration, cache writer, save/regenerate, file watcher;
- macro execution + the Pass-1 expand loop; CLI parsing; the exe-bundle startup stub;
- platform-DLL **load orchestration** (`load_platform_dll`, `/platform-schema`) and the
  `ABI_VERSION` loader gate; observability ring buffers (`io_trace`/`scheduler_trace`/`got_trace`).

**`/int` is a host-CLIENT of the IO/RC runtime library, not its owner.** How IO is managed at
run time — the reactor, async trampoline, `consume_io_tree`, permit pools, RC/drop discipline,
lifetime-across-suspension — is a runtime-library implementation detail encapsulated in
**`cranelisp-intrinsics`** (`design/intrinsics/reactor.md`), which `cranelisp-backend` emits
calls into (BC §4b). `/int`'s only contact with that runtime is the **thin host-client seam**
(`reactor.md §0`): it constructs the reactor once through the single C-ABI entry
`cranelisp_run_io`, drives `block_on_reactor` for `--run`/REPL, propagates the loader ABI
refusal, and reads the optional `/strand` dev sink. It never reaches into reactor internals.

> **Relocation pointer (S97, FIXME 0486).** The IO-runtime **reactor/trampoline interior**
> design moved out of this directory to **`design/intrinsics/reactor.md`** — it is
> backend-emitted runtime, not an int concern. The `/int` host-client role is demarcated in
> that doc's §0 and wired here by `io-integration.md` (I6/I7 IO forcing) + the platform loader.
> `bind-chain-analysis.md` (the *compile-time* IO-scheduling pass) stays here pending 0486's
> finer ownership ruling.

## What lives here (genuinely int)

- **Compiler-internal concurrency** (the scheduling axis, NOT the language-level effect
  runtime): `concurrency-architecture.md`, `concurrency-audit.md`, `concurrency-risks.md`,
  `concurrency-test-strategy.md`, `concurrent-workers.md`, `persistent-workers.md`,
  `heisenbug-race-closure.md`, `signature-body-prepass.md`, `concurrency/`.
- **Pipeline / session / REPL / cache / macro / observability**: `int.md`, `io-integration.md`
  (the host-side IO forcing + platform-DLL load wiring), `cache-hit-loading.md`,
  `session-persistence.md`, `symbol-table-cache.md`, `repl-lifecycle.md`, `observability.md`,
  `macro-resolver-impl.md`, `cranelisp-toml.md`, the `s7*`/`step*`/`wave-*` slice docs, etc.
- **`session-transaction.md`** (S101; amended S102 — §9.1.1 downgrade `stale:` contract,
  §10 T1 full-cure mechanics) — the R3 dev-session redefinition machinery:
  summary-diff gate, reverse dependency index, dependent-recompilation transaction,
  BROKEN/trap-stub cascade management, ABI-epoch slot versioning bookkeeping + retention
  pools, persistence pins. Consumes the pinned backend interface
  (`design/backend/ownership-codegen.md` §8.3); scope authority
  `design/arch/ownership-inference.md` §5.
- **`s102-defect-wave.md`** (S102) — the Block-A /int defect-wave cluster designs:
  T1 downgrade print + full-cure sizing verdict, persistence integrity (D1/D2/0489),
  file-backed dev-loop (D3/0487), display/diagnostic batch (0486/0491/trap-format/
  0490/0484), and the Principle-23 scenario-space matrices feeding FIXME 0496.
- **`bind-chain-analysis.md`** — the compile-time automatic-IO-scheduling pass (§10.12); its
  finer ownership is an open FIXME 0486 question, left here pending that ruling.

## Document index (durable vs historical) — the triage of record

Maintained by `/design` (int); triaged S110, FIXME 0607 (the S109 typecheck 0578 template).
An agent designing against this surface reads the **durable** docs; the **historical** docs
are retained for the audit trail only and each carries a top-of-file `HISTORICAL` banner — do
not treat them as current design intent. When a durable doc, a historical doc, and the current
source disagree, the **source + the master win**.

**Master.** `int.md` — the single source of design intent for the binary surface; every other
doc is subordinate.

**Durable subsystem docs** (one-per-subsystem, current):
`concurrency-architecture.md` (the compiler-internal scheduling axis),
`signature-body-prepass.md` (the S93 two-phase barrier — the durable race cure),
`session-transaction.md` (S101 dev-session dependent-recompilation; `redefine.rs`),
`session-persistence.md`, `symbol-table-cache.md`, `cache-hit-loading.md`,
`io-integration.md` (host-side IO forcing + platform-DLL wiring),
`bind-chain-analysis.md` (compile-time auto-IO scheduling; §10.12),
`observability.md` (the trace/event sinks), `macro-resolver-impl.md`, `cranelisp-toml.md`,
`repl-lifecycle.md`, `agent.md` (the embedded-agent + `/search` index design — large, active),
`terminal-styling.md` (the `styled::render` role-span seam).

**Active subordinate feature docs** (scoped, live):
`index-worker-isolation.md` (S110, FIXME 0604 — the index-feed isolation contract),
`repl-decomposition.md` (S110, FIXME 0606 — the `repl.rs` module-cut sign-off),
`quote-shield.md` (S111, FIXME 0613 — `expand_scoped` holds quoted data out of Pass-1
macro expansion; the int leg of the quasiquote-legal-everywhere wave),
`macro-diagnostic-reanchoring.md` (S113, FIXME 0650 — the int-side re-anchoring seam:
synthetic-span diagnostics over macro-expansion output relocate to the origin form;
paired with `design/frontend/binder-head-reject.md`),
`multi-sig-introspection.md` (S113 — extended with the D1 constraint-display
read-follow, §2.4), `private-submodule-import.md`, `symbol-table-generics.md`,
`bare-primitive-value-path.md`.

**Reference lineage** (heavy race/audit records — load-bearing as precedent, not day-to-day
design intent): `heisenbug-race-closure.md` (S61 per-interleaving-treadmill record — the
lineage `index-worker-isolation.md` and `signature-body-prepass.md` cite), `concurrency-audit.md`,
`concurrency-risks.md`, `concurrency-test-strategy.md`, `concurrent-workers.md`,
`persistent-workers.md`, `concurrency/`.

**Historical working / slice docs** (`HISTORICAL`-bannered S110; completed or superseded,
audit trail only): `step4-macro-blocking.md`, `step5-lazy-discovery.md`, `step7-repl-eval.md`,
`step8-platform-registry.md`, `step9-error-cascade.md`, `s76-implementation-plan.md`,
`s77-int-restructure.md`, `s78-implementation.md`, `s78-entry-module.md` (its §2
prelude-fallback mechanism is now canonical in `design/arch/prelude-import-convergence.md` +
`src/CLAUDE.md`), `s87-decomposition.md`, `s102-defect-wave.md`, `wave-3a-process-form.md`,
`implementation-slice-s66.md`, `phase2-codegen-convergence.md`, `pipeline-convergence.md`,
`dual-path-persistence-collapse.md`, `cache-prelude-restoration-repro.md`,
`platform-registry-removal.md`.

## Cross-references

- `design/arch/bounded-contexts.md` §6 — canonical int bounded context (cadences, handoffs, constraints).
- `design/intrinsics/reactor.md` — the IO/RC runtime library `/int` is a host-client of (§0 = the seam).
- `design/intrinsics/CLAUDE.md` — the runtime-library ownership statement (the callee side).
- `design/arch/effect-concurrency.md` — the arch-owned language-level concurrency model (distinct from int's compiler-internal scheduler).
