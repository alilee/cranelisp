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

## Cross-references

- `design/arch/bounded-contexts.md` §6 — canonical int bounded context (cadences, handoffs, constraints).
- `design/intrinsics/reactor.md` — the IO/RC runtime library `/int` is a host-client of (§0 = the seam).
- `design/intrinsics/CLAUDE.md` — the runtime-library ownership statement (the callee side).
- `design/arch/effect-concurrency.md` — the arch-owned language-level concurrency model (distinct from int's compiler-internal scheduler).
