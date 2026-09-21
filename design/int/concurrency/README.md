# Int concurrency diagrams

Structural views of the integration layer's compiler-internal concurrency, as
built. The architectural-altitude story (cadences, handoffs, windows) lives in
`design/arch/sequences/`; the prose inventory these illustrate is
`design/int/concurrency-architecture.md`.

| File | What it shows |
|---|---|
| `target-state.svg` | Int-internal architecture: session core, single dependency service, unified worker subsystem, narrowed shared-state ownership. |
| `concurrency-structure-matrix.svg` | Inventory view of the major concurrency structures inside int — owner, readers/writers, interface shape. |
| `scheduler-lifecycle.svg` | State-machine view of module lifecycle inside the scheduler: pool transitions and readiness publication points. |
| `dependency-protocol-target.svg` | The in-call-stack dependency block→resume protocol (S78): on a dependency gap the worker drops its stack-local cluster staging, registers the dep, blocks on the scheduler (cycle-check first), the pool processes the dep, `notify_typecheck_done` unblocks the waiter, and the worker retries its cluster from the top against committed live state. No `module_sexps`/`suspend_states` parking maps. See `design/int/int.md` §6.2. |
| `symbol-publication-target.svg` | Publication flow with one explicit publication authority. |
| `compilation-cadence-batch-run.svg` | One compilation-cadence batch-run pass: scheduler ↔ priority workers ↔ nice workers ↔ symbol table — the int-internal counterpart to the architectural exec-flow diagrams. |

The `-target` filenames are historical: these shapes were proposed as targets in
the S62–S78 restructure and are now as-built. They are not renamed because live
references cite them by name.

## Reading order

1. `target-state.svg` — where things sit.
2. `compilation-cadence-batch-run.svg` — how a batch run unfolds.
3. `scheduler-lifecycle.svg` — a module's path through the scheduler.
4. `dependency-protocol-target.svg` and `symbol-publication-target.svg` — the
   protocol-level invariants for the two highest-risk surfaces.
5. `concurrency-structure-matrix.svg` — inventory reference.

## Source files

Each SVG is generated from its sibling `.mmd`. Regenerate:

```bash
cd design/int/concurrency
for f in *.mmd; do mmdc -i "$f" -o "${f%.mmd}.svg"; done
```
