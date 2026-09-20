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
  `macro-resolver-impl.md`, `cranelisp-toml.md`, the `step*` slice docs, etc.
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

This memory establishes three Binary/int-owned collections:

| Collection | Purpose |
|---|---|
| `int-current-designs` | Current Binary/int master, subsystem and active feature designs for pipeline orchestration, compiler-internal scheduling, REPL/session, persistence, macro execution, host integration and observability. |
| `int-reference-lineage` | Load-bearing concurrency and race-analysis records retained as precedent for current Binary/int design. |
| `int-historical-records` | Superseded Binary/int working, migration and slice records retained solely for the audit trail described by the S110 triage. |

All three are established collections. References remain live in the current
declaration. The historical collection is the bounded candidate if the user
later approves historical-record reference policy; this memory grants no such
waiver.

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
`s122-closure.md` (S122 — **the current entry point for the selected Binary/int
closure**: source-reconciled reload-demand recovery including linked
concrete-in-place overload realizations, macro/quote ownership, canonical
result-root + `/mem`, failed-codegen evidence choice, eval-production stop, and
the continuous Phase-5 source reservation),
`s121-c6-visit.md` (S121 — the preceding complete-surface visit whose selected
remaining obligations are narrowed by `s122-closure.md`: the one
C6 binary/exe-bundle visit. Ordered bundles N1–N6, per-FIXME dispositions for
the 21 allocated records plus the C6 half of 0553, the exact `src/` reservations,
public-API/schema/ABI effects (two individually approved and baseline-confirmed
types additions; zero schema/ABI change), and the `/review` rejects and
falsifiers. Reconciled 2026-09-01: the two blockers it opened with are ruled
upstream — 0869's producer is C3's (`design/arch/trait-impl-cache-carrier.md`
§9) and 0798's scoped alias lookup is C1's walk and mint
(`design/arch/module-alias-scoped-lookup.md`) — so N3's entry gates are
ordinary wash landings and nothing is owed to C6),
`index-worker-isolation.md` (S110, FIXME 0604 — the index-feed isolation contract),
`quote-shield.md` (S111, FIXME 0613 — `expand_scoped` holds quoted data out of Pass-1
macro expansion; the int leg of the quasiquote-legal-everywhere wave),
`macro-diagnostic-reanchoring.md` (S113, FIXME 0650 — the int-side re-anchoring seam:
synthetic-span diagnostics over macro-expansion output relocate to the origin form;
paired with `design/frontend/binder-head-reject.md`; §2.1 S114 extends the same
transform to the def/const finalize/typecheck-error path),
`macro-turn-ownership.md` (S119/S122, FIXME 0889 — **the** delivered macro-turn ownership
protocol: single-owner marshalling, transfer-by-ABI-
crossing, exactly-once result discharge through `consume_sexp`, the
`MacroClauseAbi` ownership declaration [Rule 0], the arena/epoch rejection, and
the §9 S121 macro-checkpoint interaction surface; §8 is the `/dev` gate set,
D0/D1 binding),
`macro-marshal-rc-protection.md` (S114, FIXME 0638 — the marshal-boundary RC
contract: deep protection of the whole marshalled arg tree, curing the macro-clause
interior-alias double-free. **§2's mechanism is SUPERSEDED by
`macro-turn-ownership.md` Rule 2 (S119)**; read it for the 0638 diagnosis and the
negative-control-twin argument, not as current mechanism),
`expansion-qualification-scope.md` (S114, FIXME 0670 — `qualify_expanded_sexp`
becomes scope-aware, skipping value-level binder slots; wave-1 of the F8 chain,
paired with frontend `binder-head-reject.md` re-landing),
`prelude-table-write-isolation.md` (S114/S115/S121, FIXMEs 0604 + 0740 + 0793 —
the foreground public-write chokepoint contract; companion to
`index-worker-isolation.md`'s background half; S115 corrected the predicate to
declared-export closure and routed `commit_staging_to_live`; **S121 closed the
census** with the three session-init rows, the scope-boundary statement, the two
factual corrections 0740 carried, and candidate-batch validation before table
or GOT publication; the retired 0604/0740/0793/0818 group now has its closure
and historical attribution limits in `design/arch/bounded-contexts.md` §6),
`impl-redefinition-hot-reload.md` (S115, FIXME 0714 / spec §5.4.5 — a same-type
re-impl hot-reloads via the existing `commit_staging_to_live`→`commit_slotted_def`
GOT-patch path; the silent-ignore locus is the `derive_codegen_batch` TraitImpl
arm; no impl-specific parallel path, P11),
`result-owner.md` (S116, refreshed S118 — FIXME 0745 / arch ruling 9: the ONE
program-result owner across REPL / `--run` / cache-hit / linked startup —
observe-then-release, exact-once, type-directed via backend's canonical per-concrete
glue; three resolution adapters, no second heap-type predicate; §8 is the serial
implementation order, §9 the flip set + armed acceptance leg),
`s117-conformance-recovery.md` (S117, amended S121 — the ordinary W3a
prepared-turn transaction [prepare → whole-batch codegen → publish, one cadence
for eval and worker], W3b presentation readers, and the current source-ordered
macro checkpoint at §1.1.2/§2.1: complete macro-local typecheck+codegen,
immediate one-module publication, source-continuation retry and deletion of the
former temporary world; §6 carries presentation),
`multi-sig-introspection.md` (S113 — extended with the D1 constraint-display
read-follow, §2.4), `private-submodule-import.md`, `symbol-table-generics.md`.

**Reference lineage** (heavy race/audit records — load-bearing as precedent, not day-to-day
design intent): `heisenbug-race-closure.md` (S61 per-interleaving-treadmill record — the
lineage `index-worker-isolation.md` and `signature-body-prepass.md` cite), `concurrency-audit.md`,
`concurrency-risks.md`, `concurrency-test-strategy.md`, `concurrent-workers.md`,
`persistent-workers.md`, `concurrency/`.

**Historical working / slice docs** (`HISTORICAL`-bannered S110; completed or superseded,
audit trail only): `step4-macro-blocking.md`, `step5-lazy-discovery.md`, `step7-repl-eval.md`,
`step8-platform-registry.md`, `step9-error-cascade.md`, `s102-defect-wave.md`,
`cache-prelude-restoration-repro.md`, `platform-registry-removal.md`.

**Redirections.** Landed-migration records deleted at S122 (Git retains them); a citation to
one of them reads instead: `phase2-codegen-convergence.md` → `int.md`
§4.1/§4.2/§5/§7 (`Code` home, single writer, cache-hit regeneration);
`dual-path-persistence-collapse.md` → `int.md` §6.1 (single `register_module` recursion,
the `delays_other` rule) and §7.1; `pipeline-convergence.md` → root `CLAUDE.md` §Pipeline
and [project-root resolution](repl-lifecycle.md#6-project-root-resolution) (project root = cwd);
`s77-int-restructure.md`, `s78-implementation.md`, `wave-3a-process-form.md`,
`s76-implementation-plan.md` → `int.md` §6.2 (cluster core, wrappers, concurrency
invariant, codegen batch); `s78-entry-module.md` → `int.md` §6.5 and
`design/arch/prelude-import-convergence.md`; `repl-decomposition.md`,
`s87-decomposition.md` → `int.md` §3.2/§3.3; `bare-primitive-value-path.md` → `int.md` §3.3
(display provenance).

## Cross-references

- `design/arch/bounded-contexts.md` §6 — canonical int bounded context (cadences, handoffs, constraints).
- `design/intrinsics/reactor.md` — the IO/RC runtime library `/int` is a host-client of (§0 = the seam).
- `design/intrinsics/CLAUDE.md` — the runtime-library ownership statement (the callee side).
- `design/arch/effect-concurrency.md` — the arch-owned language-level concurrency model (distinct from int's compiler-internal scheduler).
