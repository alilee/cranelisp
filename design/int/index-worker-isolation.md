# Index-feed isolation — the background indexer writes nothing the foreground reads

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

**INDEX-ISOLATION.** No index branch writes state that a foreground compile
reads, in memory or on disk. Every intermediate the index typecheck needs is
a function-local discard substrate, dropped before the task returns. The feed
writes only `importable_indices`.

The cache (`.meta`, `.o` and manifest) is foreground-written. The feed may
read a `.meta` that the manifest validates (agent.md §25.1, branch (b)); it
never writes one (§3.3).

## 3. Realisation

### 3.1 Private tables and aliases

> **Designed change (S125; not in source).** A dependency that is absent or
> unpublished in the copy no longer skips the module (ACT-1092). The private
> substrate gains the dependency's table, from live, a validated `.meta` or
> a private index from source; a dependency still compiling defers the
> module. See [the binary clean and green](s125-binary-clean.md) §5.3.

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

The feed writes no cache artefact (ACT-1083). **Status: built at
`f2317af0`.** Branch (c) wrote a `.meta` and a manifest entry for a clean,
macro-free module; that write is removed.

- **The fault.** The write re-keyed a stale importer's manifest entry and
  rewrote its `.meta`, and left the `.o` that an earlier launch built under
  the old key. The next cached launch validated the new entry and restored
  the old object: a wrong value, or a call through a retired slot. `qa`
  reproduced it as REPRO-1083, which fails on the wrong value and passes
  after the correction, read at `79a8c94c`.
  This met the former reopen trigger: an index-written record diverged
  from what the foreground writer would produce for the files beside it.
- **The rule.** The index pass writes no cache artefact. For a module whose
  entry is stale, including one whose object is stale, it typechecks on the
  private substrate (§3.1), records rows, and leaves the `.meta`, the `.o`
  and the manifest entry as it found them. The next foreground load misses on
  the stale entry and rebuilds. What must be true of the files the foreground
  writes is [int.md §7.7](int.md#77-one-generation-beside-an-entry-act-1083).
- **Why removal rather than repair.** The write is redundant as well as
  unsound:
  - *No sound foreground hit.* An index-written `.meta` has no object. For a
    module with codegen targets, the restore's object gate misses (int.md
    §7.1, *Generic-only modules have no object*). So the write produced a
    hit only for a generic-only module, and that restore walked none of its
    dependencies, because the index table carries no structural
    declarations. Otherwise it produced a hit only beside a stale object,
    which is this fault.
    - Observed by `design`, 2026-11-18, on the debug build of `a205a29f`.
      After a `/search` session indexed `mathx`, which has one concrete
      `defn`, a REPL import of `mathx` printed the `.meta valid` trace and
      then built `mathx` fresh: its `.o` first appeared after that session.
      The trace prints before the object gate.
  - *No measured index warm start.* On 60 project-root modules of 20
    concrete `defn`s each, the debug build's REPL burn-down took 0.44 to 0.46 s cold
    and the same warm with index-written `.meta`s. With `--no-cache`, where
    every module takes branch (c) and nothing is written, it took 0.27 to 0.28 s.
  - *Repair would add mechanism.* Making the index write consistent would
    mean deleting a foreground object from the background. A module can be
    registered between the index's registry check and its write, so that
    deletion races the nice worker's write of a fresh object.
  - ACT-0952 already forbids the successor index from publishing cache
    artefacts until it runs the complete compiler protocol.
- **Cost.** `--run`, `--link` and release builds never arm the index, so
  their warm start can only lose stale hits. A REPL session re-typechecks
  on the private substrate each reachable module that no foreground run
  compiled, every session, on a nice worker that yields to object codegen
  (agent.md §25.5). The REPL prompt does not wait on it.
  - *Falsifier.* With the write removed, a REPL session's first `/search` over
    a project's reachable modules shows the not-ready note where the build
    with the write showed complete results, or the burn-down time on a second
    session rises materially above the first-session time with the write.
  - *Potential extension.* An index-private warm store, which a foreground
    compile never reads. *Trigger:* that falsifier observed.
- **As built** (`f2317af0`; `src/session_v4/index_worker.rs`,
  `src/cache/dependency_record.rs`). The write, its call and the data only it
  read are gone: the checked module's source hash, and the declaration edges
  and macro flag of the record. `ModuleEdges::of_declarations` is private to
  `of_table`, and the index worker's edge-record unit rows retired with the
  write. Module row M-1083,
  `an_index_pass_over_a_stale_cached_module_writes_no_cache_artefact`:
  - an index pass over a module whose manifest entry is stale and whose `.o`
    exists leaves the entry, the `.meta` and the `.o` unchanged, and a
    validation of the module after it is stale. It turns RED when the write
    is restored;
  - negative: the same pass still records the module's rows.
- **End-to-end.** Turn green: `tests/cache.rs::cache_index_over_stale_importer_preserves_calls_across_modes`
  (REPRO-1083). Stay green: its two controls,
  `cache_index_stale_importer_no_session_control` and
  `cache_index_stale_importer_same_order_control`, and the K-6 cell
  `cache_restored_text_after_abi_change_preserves_importer_calls_across_modes`,
  whose loaded reading `qa` takes.
- **Former pins of the removed write.** `test` restated the
  `tests/search.rs` cells that asserted or leaned on the index `.meta` at
  `96d4677c`, among them
  `search_branch_c_stale_meta_typechecks_without_cache_write` and
  `search_index_to_import_compiles_without_index_cache`.

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
   `record_entries`, `mark_skipped`) and the read-only projection of
   already-loaded tables. No index branch calls a cache writer: the
   `ObjectCache` `.meta` writer, the manifest record builder or a file write
   under the cache directory (§3.3). A violation is a Blocker.
