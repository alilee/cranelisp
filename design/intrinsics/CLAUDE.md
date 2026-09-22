# design/intrinsics/

Interior design for `cranelisp-intrinsics`, the runtime library that
`cranelisp-backend` emits calls into: heap ownership and disposal, the IO
reactor and trampoline, the intrinsic catalog and the memory-safety diagnostics.
Owned by `/design` narrow-deployed to the primitives + intrinsics surface
(`sprints/METHOD.md` §1.1).

The bounded context, its invariants and its sibling `cranelisp-primitives` are
[bounded-contexts §4a/§4b](../arch/bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics).
Source conventions and debug hooks are in
[the crate memory](../../crates/cranelisp-intrinsics/CLAUDE.md).

## Boundaries worth knowing before editing

- **The binary is a host client, not an owner.** `src/` forces IO trees through
  `cranelisp_run_io` and never constructs reactor, pool or supervisor state
  ([`reactor.md`](reactor.md) §0). Reactor internals are this directory's.
- **Host-promised externs that must name compiler types live in `src/`** (for
  example `discover-tests`, which names `Code`). They belong to `design/int/`,
  not to this crate's catalog.
- **Cross-pair contracts live in `design/runtime/`**, not here:
  `s119-typed-consume-funnel.md` (the `Owned`/`Borrowed` handle contract) and
  `s118-structural-embedding-ownership.md` (the consume-owner contract). This
  directory implements them without restating them.

## Documents

This memory establishes one collection:

| Collection | Purpose | Boundary |
|---|---|---|
| `intrinsics-current-designs` | Current intrinsics interior designs for runtime heap ownership, node disposal, IO execution, intrinsic registration and diagnostics. | The four named current Markdown products directly under `design/intrinsics/`. |

`intrinsics-current-designs` is established and retains live reference checking.

| File | Purpose |
|---|---|
| [`ownership-and-disposal.md`](ownership-and-disposal.md) | Counted references in Rust bodies, the blessed increment, structural teardown of the `Sexp` and IO families, trampoline ownership transitions and result-disposal authority |
| [`reactor.md`](reactor.md) | The reactor, async trampoline and executor; the `ctx` vtable and permit pool; `Par`, launch, supervisor and `race`/`select`; cancellation release paths; liveness |
| [`intrinsics-table.md`](intrinsics-table.md) | The published `intrinsics_table()` import catalog and its consumer contract |
| [`diagnostic-modes.md`](diagnostic-modes.md) | The M1/M2/M3 allocator modes, the A1–A4 seam checks and their precheck ordering, and the test-only fault-plant protocol with its arming discipline |

Section numbers in `reactor.md` and `diagnostic-modes.md` are cited from
source comments; keep them stable when editing.

## Related designs

- `design/arch/effect-concurrency.md` — the concurrency model the reactor
  implements.
- `design/backend/io-trampoline.md` — the emitted IO nodes this runtime
  interprets.
- `design/platform/poll-leaf-authoring.md` — the platform half of the `ctx`
  vtable.
- `design/int/io-integration.md` — the host-client side.
