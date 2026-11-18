---
id: ACT-1083
title: A REPL session's index pass records a stale module as current and leaves its old object in the cache, so the next launch runs code compiled against a dependency that has since changed
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-18
refers_to:
  - src/session_v4/index_worker.rs
  - src/cache/dependency_record.rs
  - design/int/index-worker-isolation.md
  - design/int/int.md
  - tests/cache.rs
  - tests/plan/s124-evidence-delta.md
---

## Observation

`qa`, 2026-11-18, the debug build of `a205a29f`, no prelude, each run in
its own directory. The counts by build are also in the
[S124 evidence delta §14.7](../../tests/plan/s124-evidence-delta.md#147-defects-and-leads-read-at-this-exit).

**A deterministic program.** Three files: `user.cl` holds
`(defn f [] 41)` then `(defn h [] 7)`; `lib.cl` imports `user`'s `f` and
defines `(defn g [] (f))`; `app.cl` imports `lib`'s `g` and returns
`(Pure (g))`.

1. `--run app.cl` exits 41 and caches all three modules.
2. `user.cl` is rewritten with the two definitions in the other order. The
   program's meaning is unchanged.
3. A REPL session starts in the directory, runs `/search g`, and ends. Its
   output lists `g` in `lib`.
4. `--run app.cl` exits **7**. `--no-cache --run app.cl` exits 41.

20 of 20 runs alone and 200 of 200 under 28 parallel processes give 7.

**At the seam.** After step 3 the manifest entry for `lib` records `user`
at the key of the rewritten file, `lib.meta.json` is rewritten, and
`lib.o` is byte-identical to the object step 1 wrote. Step 4 validates
`lib` against that entry and restores the old object, whose `g` calls
`user`'s slot 0. Slot 0 now holds `h`.

**Controls,** each differing from the subject in one step:

| Control | `lib`'s entry after step 3 | `lib.o` at step 4 | Exit | Runs |
|---|---|---|---|---|
| No REPL session (step 3 omitted) | the old key | rebuilt | 41 | 200 of 200 under load |
| `lib.o` deleted after step 3 | the new key | rebuilt | 41 | 1 |
| Step 2 edits `h`'s body and keeps the order | the new key | the old object, restored | 41 | 1 |

The third control restores the same stale object and passes only because
no slot moved.

## The cell that showed it

`tests/cache.rs::cache_restored_text_after_abi_change_preserves_importer_calls_across_modes`
(K-6, ACT-1052's guard) ends on signal 11 in its cached `--run`, linked
and REPL legs in about one loaded run in ten. Its second leg is a REPL
session that changes `f` from `Int` to `String` and back, which moves `f`
from slot 0 to slot 2 and leaves `user.cl` byte-identical.

In 300 loaded runs of its first four legs, 29 ended on the signal. The
key the session left for `lib` separates them exactly:

| `lib`'s entry after the session records `user` at | Runs | Cached `--run` |
|---|---|---|
| the reverted text with slot 2 (the state at exit) | 29 | signal 11, 29 of 29 |
| any of four earlier or mixed states, or the entry untouched | 271 | 41, 271 of 271 |

`lib.o` is the first launch's object in all 300. The index pass runs once
per session, at a moment that varies with load. Only a pass that runs
after both edits records the state the next launch sees.

## Classification

- **A defect, and not ACT-1052's.** ACT-1052's correction keys each
  recorded member by source hash and slot layout, and that key is right in
  every run above. This writer stores a correct key beside an object that
  was not built under it. The deterministic program has no REPL edit, no
  revert and no retired slot.
- **Not a test artefact.** Every run has its own directory and cache; no
  two processes share one.
- **Class:** `partial-record-update`. The manifest entry and `.meta` move
  to a new generation and the `.o` stays at the previous one. Faces: a
  wrong value, or a call through a retired slot (`null-got-slot`, signal).
- **Reach.** Any project with an importer cached by an earlier launch,
  where a dependency then changes and a REPL session runs in that
  directory before the next cached launch. A slot move gives a wrong value
  or a crash. Any other difference the old object embeds is restored the
  same way and was not probed.

## Attribution

- **Mechanism: confirmed** to the extent the controls show: the entry is
  re-keyed while the object stays, and the stale object is then restored.
  *Refuted if* a build whose index pass writes no manifest entry over an
  existing object still gives 7.
- **Writer: read in source, not observed by a planted fault.**
  `src/session_v4/index_worker.rs::write_index_meta` (branch (c): a stale
  or absent `.meta`) writes the `.meta` and calls
  `record_manifest_entry` with the current keys. Its contract is "no
  `.o`"; it does not remove one that an earlier launch wrote. `dev` probes
  this before building on it.
- **Entered: before S124.** Builds read on both programs:

| Build | Deterministic program, cached launch | K-6 legs 1 to 4, 300 loaded runs |
|---|---|---|
| `5b1a843b` (before the S122 dependency record) | 7 with and without the session: the importer restored unvalidated (CD-1) | signal in 300 |
| `94486f24` (S122 checkpoint) | refused: `unresolved symbol: __cranelisp_got_user`; 41 without the session | signal in 285, refused in 4 |
| `e294852f` (before ACT-1052's correction) | 7; 41 without the session | signal in 287, and 3 of 3 alone |
| `3c4c0f7b` (the correction) | 7; 41 without the session | signal in 27 |
| `2d3a5b3e` | 7; 41 without the session | signal in 24 |
| `a205a29f` | 7; 41 without the session | signal in 29 |

  The two signatures differ at the seam. Before ACT-1052's correction the
  entry holds a bare source hash that the revert restores, so K-6 fails
  with the entry untouched and fails alone. From `3c4c0f7b` it fails only
  when the index pass has re-keyed the entry.
- **Why coverage missed it.** K-6 was accepted green on one full run at
  `2d3a5b3e`, where it fails about one loaded run in twelve. No cell runs
  an index pass over a stale importer whose object is cached.
  [Index-worker isolation §3.3](../../design/int/index-worker-isolation.md#33-the-cache-channel)
  states the write as "no `.o`" and its premise as equality with a real
  typecheck; neither covers an object already present.
- **Owner:** `design`(int) places the correction; §3.3 carries a reopen
  trigger for removing the write. `dev`(`src/`) builds it.

## Leads, not classified

- In 51 of the 300 runs the entry's key pairs a source hash and a slot
  layout from different moments of the session (for example the `String`
  text's hash with the post-revert layout). No such key matched a real
  state here.
- `review` (static, on `9580856a` and `a205a29f`): `src/worker.rs`
  rereads a module's `.meta` for object loading and applies its slot
  assignments to the live GOT. No run above needs a replacement between
  validation and that read to explain it; the lead is neither confirmed
  nor refuted.

## Evidence allocation

- **`test`: REPRO-1083,** in `tests/cache.rs`, as
  [§14.3](../../tests/plan/s124-evidence-delta.md#143-returned-to-test)
  states it. Expected RED on exit 7.
- **`dev`(`src/`): module row M-1083.** After an index pass over a module
  whose cached object was built under another key, validation does not
  report that object as restorable. It fails on revert of the correction.
- **`qa`: the aggregate.** The 300-run loaded reading of K-6's legs on the
  corrected build, against 29 of 300 at `a205a29f`.

## Completion evidence

REPRO-1083 fails on the wrong value and passes after the correction with
both controls unchanged; M-1083 is in source; K-6's loaded reading is 0 of
300; `qa` judges adequacy and deletes this action.
