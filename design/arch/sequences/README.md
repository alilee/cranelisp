# Architectural Sequence Diagrams

This directory holds the architectural-altitude sequence diagrams for cranelisp. They use the vocabulary established in `../bounded-contexts.md` and `../overview.md` — *cadence*, *handoff*, *window*.

Two diagram families. Each `.mmd` file is paired with a generated `.svg`.

## Concurrency-invariant diagrams

Each diagram makes one concurrency invariant visible. The actor grain is the *unit of concurrency* (often finer than a data structure — for example, a single symbol-table entry or a single GOT slot), so that exclusive write authority shows up as non-overlapping activity on a lifeline. A diagram IS the proof sketch for its invariant: read it and check that the claim holds.

| File | Invariant |
|---|---|
| `concurrency-symbol-table-entry.svg` | A symbol-table entry has at most one writer per phase. Typecheck and codegen of the same entry never overlap. |
| `concurrency-got-slot.svg` | A GOT slot is single-writer per slot, atomic-readable by many. The atomic store is the cross-thread publication primitive. |
| `concurrency-dependency-service.svg` | The dependency service is the sole writer of dependency state. Workers do not poll or read shared state. |
| `concurrency-repl-session.svg` | Session state is REPL-thread-exclusive. Workers reach in only via handoffs. |
| `concurrency-watcher-channel.svg` | The watcher channel is single-writer (OS callback thread) and single-reader (REPL thread, at prompt boundary). |
| `concurrency-jit-retention.svg` | JIT pages free only when no derivative code pointer is reachable. The Arc-wrapped Jit is the retention root; swap-before-drop ordering preserves safety. |

## Execution-flow diagrams

Each diagram is a temporal walkthrough of one execution mode. The actor grain is the *cadence* (one lane per cadence). These diagrams answer "what happens" rather than "why is it safe".

| File | Mode |
|---|---|
| `exec-flow-repl.svg` | REPL session — all four cadences active (compilation, REPL, watcher, runtime). |
| `exec-flow-run.svg` | `--run` — compilation and runtime cadences only; no REPL or watcher. |
| `exec-flow-link.svg` | `--link` — compilation cadence only; runtime cadence activates only when the produced binary is later executed. |

## Reading order for a newcomer

1. `../overview.md` — establishes the vocabulary.
2. `exec-flow-repl.svg` — the maximal execution scenario; introduces the cadences in motion.
3. `exec-flow-run.svg` and `exec-flow-link.svg` — narrower modes, easier once REPL is understood.
4. The six concurrency-invariant diagrams — verify the correctness claims.
5. `../facades/{crate}.md` — once the choreography is in mind, the typed Rust signatures fall into place.

## Regenerating

```bash
cd design/arch/sequences
for f in *.mmd; do mmdc -i "$f" -o "${f%.mmd}.svg"; done
```
