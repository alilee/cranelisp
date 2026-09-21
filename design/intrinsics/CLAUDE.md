# design/intrinsics/

Interior design for the **`cranelisp-intrinsics` crate — the backend-emitted IO/RC runtime
library**. Canonical bounded context: `design/arch/bounded-contexts.md` §4b (intrinsics) +
§4a (its sibling `cranelisp-primitives`).

## Ownership — the runtime library, not orchestration

`cranelisp-intrinsics` (with `cranelisp-primitives`) is the language's **runtime library**:
the code the compiled program invokes at run time — the analog of a GC / async executor.
`cranelisp-backend` **depends on it and emits calls into it** (BC §4b invariant 1:
"backend-emitted-call targets only … called by JIT-emitted code or by the IO trampoline";
§4b: "primitive emission goes through `cranelisp-primitives` + `cranelisp-intrinsics`
directly"; §4b invariant 2: "intrinsics owns" the runtime heap layout). Nothing here is
callable from user code; nothing here knows about compilation, the REPL, the pipeline, or
development tooling.

**This is NOT an `/int` concern.** `/int` (`design/int/`, `src/`) is the *host* — the
orchestrator + application root — and is only a **host-client** of this runtime: it
constructs the reactor once through the single C-ABI entry `cranelisp_run_io` and drives
`block_on_reactor` for `--run`/REPL (`reactor.md §0`). The reactor internals — lifetime
discipline, permit pools, `consume_io_tree`, poll deferral — are runtime-library guts `/int`
neither owns nor needs to understand.

The genuinely int-owned runtime surface is only the small `int_intrinsics()`-style externs
that **physically live in `src/`** (e.g. the `discover-tests` host-promised extern, which must
name `Code` and so cannot live in this crate — Principle 18 / Decision 0048). Those are int's;
this crate's `intrinsics_table()` catalog is not.

## Documents here

This memory establishes one intrinsics-owned collection:

| Collection | Purpose | Boundary |
|---|---|---|
| `intrinsics-current-designs` | Current intrinsics interior designs for runtime heap ownership, node disposal, IO execution, intrinsic registration and diagnostics. | The four named current Markdown products directly under `design/intrinsics/`. |

`intrinsics-current-designs` is established and retains live reference checking.

| File | Purpose |
|---|---|
| `ownership-and-disposal.md` | How this crate holds, mints and releases counted heap references: the `Owned`/`Borrowed` vocabulary and its executably-enumerated trusted base, `rc_inc` as the blessed inc entry point, the structural discharge mechanism and the two family tag tables, `free_io_node`, the `Pure` payload witness and the `Effect` thunk's teardown discharge, the trampoline's fresh-`Bind` ownership rule, and result-handoff disposal authority. Evidence and open acceptance are in §8. |
| `reactor.md` | The effect reactor + async-trampoline interior — reactor loop, `HostCtx`/waker C-ABI, `EffectPoll`, the two-pool `Par` join, the token-capacity permit pool, launch/supervisor/admission, the combinator runtime, the cancellation drop-paths and the rayon→reactor bridge join. **§0 demarcates the thin `/int` host-client seam**; everything else is runtime-library interior. |
| `intrinsics-table.md` | The published `intrinsics_table()` Import catalog (BC §4b invariant 11): the entry shape, the consumer contract at the three resolution points, the emitted-call name agreement, and this crate's half of the backend import roster (§6) including why `vec-len` joins neither half. The row inventory lives in source, pinned by the closed-set guard. |
| `diagnostic-modes.md` | The implemented M1/M2/M3 modes and RC/alloc seam asserts, the closed test-only fault-plant protocol (§7) with its lane-scoped arming invariant and precheck ordering, and the landed single-owner convergence (§9). Carries the §7.5 `header_size_plausible` predicate and §7.1's plant config-error timing rule. |

## Cross-references

- `design/arch/bounded-contexts.md` §4b (intrinsics) / §4a (primitives) — canonical bounded context + invariants.
- `design/runtime/s119-typed-consume-funnel.md` — the **cross-pair** typed
  handle contract (`Owned`/`Borrowed`, the derived shim fact, the counted
  trusted base). Homed in `design/runtime/` for the same reason its S117/S118
  siblings are: it spans the pair. The intrinsics interior that implements it is
  `ownership-and-disposal.md`; crate-specific consumer visits consume that
  contract without redefining it.
- `design/runtime/s118-structural-embedding-ownership.md` — the **runtime-pair**
  consume-owner contract (FIXME 0835). It is homed in `design/runtime/` (the
  `s117-primitives-integrity.md` precedent) because it spans the pair: the
  producer seams are in `cranelisp-primitives::marshal`, while
  `cranelisp-intrinsics::drop::consume_slist` is the *authority* the contract is
  written against — ruled CORRECT and explicitly unchanged. Read it before
  touching any `consume_*` ownership semantics.
- `design/arch/effect-concurrency.md` — the arch-owned language-level concurrency model (Appendix B is the reactor's canonical plan; this dir is the crate interior beneath it).
- `design/backend/io-trampoline.md` — the backend counterpart: the codegen that emits the reified IO data + RC/drop discipline the runtime here interprets.
- `design/int/` — the **host-client** side (session drives IO forcing; platform-DLL load; `--run`/REPL wiring). See `design/int/io-integration.md`.
