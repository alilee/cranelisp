# Architectural Sequence Diagrams

This directory holds the architectural-altitude sequence diagrams for cranelisp. They use the vocabulary established in `../bounded-contexts.md` and `../overview.md` — *cadence*, *handoff*, *window*.

Two diagram families. Each `.mmd` file is paired with a generated `.svg`.

## Concurrency-invariant diagrams

Each diagram makes one concurrency invariant visible. The actor grain is the *unit of concurrency* (often finer than a data structure — for example, a single symbol-table entry or a single GOT slot), so that exclusive write authority shows up as non-overlapping activity on a lifeline. A diagram IS the proof sketch for its invariant: read it and check that the claim holds.

| File | Invariant |
|---|---|
| `concurrency-symbol-table-entry.svg` | A symbol-table entry has at most one writer per phase. Typecheck and codegen of the same entry never overlap. |
| `concurrency-got-slot.svg` | A GOT slot is single-writer per slot, atomic-readable by many. The atomic store is the cross-thread publication primitive. |
| `concurrency-dependency-service.svg` | The dependency service is the sole writer of dependency state. Workers do not poll or read shared state. **Reconciled S93** to the signature/body **pre-pass barrier** (resolved-by-deletion S93; was FIXME 0425 item 1 + 0426): all signatures register before any body typechecks, retiring the per-symbol wait/notify race window. |
| `concurrency-watcher-channel.svg` | The watcher channel is single-writer (OS callback thread) and single-reader (REPL thread, at prompt boundary). |
| `concurrency-jit-retention.svg` | JIT pages free only when no derivative code pointer is reachable. The Arc-wrapped Jit is the retention root; swap-before-drop ordering preserves safety. |
| `concurrency-scheduler.svg` | **(S93, effect-concurrency slice-2 TARGET)** The async trampoline scheduler over a host-owned reactor — the single serializing interpreter (`async fn`) polls C-ABI async-leaf platforms (`cranelisp_platform::PollFn`), which register interest via the host `HostCtx` vtable + `Waker` on `WouldBlock`; the host reactor re-polls. Each arrow is the annotation site for the strand-correlated `cranelisp_intrinsics::StrandEvent` observability stream (§11). |

## Execution-flow diagrams

Each diagram is a temporal walkthrough of one execution mode. The actor grain is the *cadence* (one lane per cadence). These diagrams answer "what happens" rather than "why is it safe".

| File | Mode |
|---|---|
| `exec-flow-repl.svg` | REPL session — all four cadences active (compilation, REPL, watcher, runtime). |
| `exec-flow-run.svg` | `--run` — compilation and runtime cadences only; no REPL or watcher. |
| `exec-flow-link.svg` | `--link` — compilation cadence only; runtime cadence activates only when the produced binary is later executed. |
| `exec-flow-compilation.svg` | Compilation cadence in isolation — scheduler, priority/nice workers, Phase 0 (synchronous parse + structural decls) then form-by-form typecheck + JIT + object codegen with cache-hit / cache-miss branches. |
| `exec-flow-runtime.svg` | Runtime + platform cadence in isolation — trampoline entry, JIT'd user code, RC inc/dec, heap allocator, cross-module GOT dispatch, IO trampoline (Pure / Effect / Bind / Par) with platform-DLL effect calls. |

## Reading order for a newcomer

1. `../overview.md` — establishes the vocabulary.
2. `exec-flow-repl.svg` — the maximal execution scenario; introduces the cadences in motion.
3. `exec-flow-run.svg` and `exec-flow-link.svg` — narrower modes, easier once REPL is understood.
4. `exec-flow-compilation.svg` and `exec-flow-runtime.svg` — the two cadences in isolation, when narrower depth is wanted than the per-mode flows.
5. The five concurrency-invariant diagrams — verify the correctness claims.
6. Crate surfaces — once the choreography is in mind, the typed Rust signatures fall into place. For most crates: `../facades/{crate}.md` (per-surface facade specs). For `cranelisp-types`: source rustdoc — `crates/cranelisp-types/src/lib.rs` module-level `//!` is the curated entry point + per-item `///` docstrings; cross-type narrative lives at `../bounded-contexts.md` §7.

## Regenerating

```bash
cd design/arch/sequences
for f in *.mmd; do mmdc -i "$f" -o "${f%.mmd}.svg"; done
```
