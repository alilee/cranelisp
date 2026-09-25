# Index-feed isolation — the background indexer never writes the foreground's in-memory state

The contract between the `/search` index feed and the foreground compile. The
index mechanism is [agent.md §25](agent.md#25-search--the-importable-symbol-index);
the architecture bounds are `design/arch/repl-embedded-agent.md` §11.

## 1. Actors

Two actors share one `Arc<SharedState>`:

- **The foreground compile**: the eval thread and the priority workers. It
  owns the live `symbol_tables`, `module_aliases`, `prelude_fallback` and the
  cache (`.meta`, `.o` and manifest).
- **The index feed**: the nice workers draining `IndexModule` tasks
  (`src/session_v4/index_worker.rs`). It runs only in the REPL and is
  best-effort. Its product is the in-memory `importable_indices` rows.

A background warm-up must never change the outcome of a foreground compile.
Isolation is by construction, not by undo: a coupling closed by cleanup
reopens through the next interleaving (`heisenbug-race-closure.md`,
`signature-body-prepass.md`).

## 2. Invariant

**INDEX-ISOLATION.** No index branch writes an in-memory `SharedState` map
that a foreground compile reads. Every intermediate the index typecheck needs
is a function-local discard substrate, dropped before the task returns. The
feed writes only `importable_indices`.

The cache is the one foreground-read channel the feed writes (§3.3).

## 3. Realisation

### 3.1 Private tables and aliases

`checked_typecheck_module` builds a private deep clone of the live symbol
tables, with the indexed module starting empty, and a fresh alias map.
`index_typecheck_into_private` runs import and export installation, macro
registration and `check_forms` against those private maps only, inside the
containment `catch_unwind` (agent.md §25.4). The typed entries are read back
from the private table, and the snapshot drops at function return.

### 3.2 Private prelude fallback

The prelude-fallback map is cloned into the same private substrate. No live
map is threaded into an install, typecheck or register call, so §5's guard is
total.

### 3.3 The cache channel

On a clean branch-(c) check of a module with no `defmacro`, the feed writes a
`.meta` (no `.o`) and, through the one record builder, a manifest entry keyed
by the source it typechecked ([int.md §7.6](int.md#76-dependency-record-and-validity)).
A later real import of that module is then a cache hit.

- **The premise is equality with a real typecheck.** It fails wherever the
  index typecheck is incomplete:
  - A macro-bearing module is typechecked without its macros, so its `.meta`
    is suppressed.
  - The index-written table carries no `imports`, `exports` or `submodules`.
    A restore from it walks none of its dependencies (int.md §16.0).
- **Status: tolerated interim.** Retiring the write reddens committed
  `tests/search.rs` pins and removes a warm-start optimisation, and no
  foreground defect has been traced to it. ACT-0952 forbids the successor
  semantic index from publishing cache artefacts until it runs the complete
  compiler protocol.
- **Reopen trigger.** Remove the write if a non-macro module's index-written
  `.meta` is observed to diverge from what the foreground writer produces.

## 4. Relation to FIXME 0604

This contract was written for the S109–S114 phantom `prelude` export, and the
feed is not its cause: the deterministic `--run --no-cache` recipe never arms
the index feed. The foreground cure is the export-closure gate,
[int.md §6.7](int.md#67-public-candidate-exposure--the-export-closure-gate).

## 5. Reviewer guard

A review of `src/session_v4/index_worker.rs` confirms INDEX-ISOLATION as
follows. Each check is on the code, not on an interleaving.

1. Every install, typecheck, register or cluster-view call reached from an
   index branch takes the private tables, aliases, prelude fallback or discard
   staging, never a live `SharedState` map. The only permitted live contact is
   the read that seeds the snapshot. A violation is a Blocker.
2. The feed writes only `importable_indices` (`record_triples`,
   `record_entries`, `mark_skipped`), the read-only projection of
   already-loaded tables, and the §3.3 cache write.
