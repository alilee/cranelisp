# Int Concurrency Diagrams

Per-crate diagrams for the integration layer's internal concurrency. The architectural-altitude story (cadences, handoffs, windows) lives in `design/arch/sequences/`; this directory carries the int-internal target structures, protocols, and the compilation-cadence-batch-run sequence.

## Active diagrams (target shape)

| File | What it shows |
|---|---|
| `target-state.svg` | High-level int-internal target architecture: smaller session core, single dependency service, unified worker subsystem, narrowed shared-state ownership. |
| `concurrency-structure-matrix.svg` | Inventory view of the major concurrency structures inside int — owner, readers/writers, interface shape. |
| `scheduler-lifecycle.svg` | State-machine view of module lifecycle inside the scheduler. Pool transitions, readiness publication points. |
| `dependency-protocol-target.svg` | Target dependency block→resume protocol, in-call-stack (option b — S78 restructure): on a dependency gap the worker drops its stack-local cluster staging, registers the dep, blocks on the scheduler (cycle-check first), the pool processes the dep, `notify_typecheck_done` unblocks the waiter, and the worker retries its cluster from the top against committed live state. No `module_sexps`/`suspend_states` parking maps. See `design/int/s77-int-restructure.md`. |
| `symbol-publication-target.svg` | Proposed target publication flow with one explicit publication authority. |
| `compilation-cadence-batch-run.svg` | Sequence diagram of one compilation-cadence batch-run pass: scheduler ↔ priority workers ↔ nice workers ↔ symbol table. The int-internal counterpart to the architectural exec-flow diagrams in `design/arch/sequences/`. |

## Reading order

1. `target-state.svg` — the structural picture of where things sit.
2. `compilation-cadence-batch-run.svg` — sequence detail of how a batch run unfolds.
3. `scheduler-lifecycle.svg` — state-machine view of a module's path through the scheduler.
4. `dependency-protocol-target.svg` and `symbol-publication-target.svg` — protocol-level invariants for the two highest-risk surfaces.
5. `concurrency-structure-matrix.svg` — inventory reference.

## Archive

`archive/` holds the pre-target snapshots — `current-state`, `dependency-protocol-current`, `symbol-publication-current`. They are kept for audit-trail value (showing the design defects the target shape closes); they are not the target architecture and should not be cited as design intent.

## Source files

Each SVG is generated from its sibling `.mmd`. Regenerate:

```bash
cd design/int/concurrency
for f in *.mmd; do mmdc -i "$f" -o "${f%.mmd}.svg"; done
```
