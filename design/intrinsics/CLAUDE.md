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
neither owns nor needs to understand. (Historical note: `reactor.md` lived under `design/int/`
until S97, when it was relocated here to stop mis-signalling `/int` ownership — see FIXME 0486.)

The genuinely int-owned runtime surface is only the small `int_intrinsics()`-style externs
that **physically live in `src/`** (e.g. the `discover-tests` host-promised extern, which must
name `Code` and so cannot live in this crate — Principle 18 / Decision 0048). Those are int's;
this crate's `intrinsics_table()` catalog is not.

## Documents here

| File | Purpose |
|---|---|
| `s121-c5-intrinsics-visit.md` | **The current visit.** Sprint 121's single design delta for this crate (stream C5): `free_io_node`; R1's three-state atomic `Pure` claim/discharge, error ferry and evidence; R2's cancelled-blocking-loser join preservation; the **one structural discharge mechanism** applied to both the `IO` and `Sexp` node families — which is where `consume_sexp`'s missing `SexpAnnotated` (tag 7) arm lands — the typed consume funnel's intrinsics half, the `vec-len` de-slot's intrinsics arm and roster handoff, and the source-backed disposition of FIXMEs 0835/0848/0859/0928/0932/0934. Carries the retained-reservation W3 braid without a second visit. |
| `reactor.md` | The slice-2 effect reactor + async-trampoline interior — reactor loop, `HostCtx`/waker C-ABI, `EffectPoll`, the two-pool `Par` join, the token-capacity permit pool, launch/supervisor/admission, the combinator runtime + cancellation drop-paths. **§0 demarcates the thin `/int` host-client seam**; everything else is runtime-library interior. Relocated from `design/int/` at S97 (FIXME 0486). |
| `intrinsics-table.md` | The published `intrinsics_table()` Import-catalog design (BC §4b invariant 11). **Landed**; its as-built correction is at the head (the catalog shipped as a `pub fn`, not the `pub static` the body target-states, per the S76 seam-3 `!Sync` ruling — read every `INTRINSICS_TABLE` as `intrinsics_table()`). §6a is this crate's half of the backend import roster and why `vec-len` joins neither half. |
| `rc-inc-entry-point.md` | The `rc_inc` blessed inc entry point (BC §4b invariant 3, the atomic-RC discipline). |
| `diagnostic-modes.md` | Implemented M1/M2/M3 and RC/alloc seam diagnostics; the closed test-only fault-plant protocol (§7, **landed S118 W2a** — all eight detection triplets, the e2e M3 cell, and the fail-on-revert records; FIXME 0848 has no source work left, and §9a's 0859 detector-as-oracle protocol is **retired unexecuted** by the 2026-09-01 user disposition) including the lane-scoped arming invariant and the precheck-ordering prerequisite; the 0850 + ruling-7 convergence batch (§9); the 0859 oracle cross-reference (§9a). Carries the two S118 W2b design rulings: §7.5's `header_size_plausible` predicate (FIXME 0879 — the alignment clause is retracted; it false-positived on ragged `HeapString` sizes) and §7.1's plant config-error timing (FIXME 0881 — the contract is state-and-action precedence, not wall-order). |
| `implementation-slice-s66.md` | Historical implementation-slice notes. |

## Cross-references

- `design/arch/bounded-contexts.md` §4b (intrinsics) / §4a (primitives) — canonical bounded context + invariants.
- `design/runtime/s119-typed-consume-funnel.md` — the **cross-pair** typed
  handle contract (`Owned`/`Borrowed`, the derived shim fact, the counted
  trusted base). Homed in `design/runtime/` for the same reason its S117/S118
  siblings are: it spans the pair. **While Sprint 121's C5 stream runs, the
  intrinsics invocation holds it** so the two crate passes cannot both rewrite
  one contract; the primitives invocation consumes it without editing. Its
  intrinsics-half implementation design is `s121-c5-intrinsics-visit.md` §6.
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
