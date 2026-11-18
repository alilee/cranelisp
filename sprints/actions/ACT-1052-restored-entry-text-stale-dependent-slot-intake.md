---
id: ACT-1052
title: A dependent's cached object may embed a moved entry slot after the entry's text is restored
status: resolved
priority: high
from: arch
to: qa
sprint: 123
filed_at: 2026-11-16
refers_to:
  - design/int/int.md
  - design/int/session-transaction.md
  - src/cache/dependency_record.rs
  - tests/plan/s123-evidence-delta.md
---

## Observation

Reproduced by `qa` on HEAD `390201c3` (`target/debug/cranelisp`),
2026-11-16. The fixture and legs are K-6 in the
[S123 evidence delta](../../tests/plan/s123-evidence-delta.md#37-committed-reds-for-carried-defects).

- **Sequence.** `app` imports `lib`, and `lib` imports `user`. A cold
  `--run app.cl` caches all three. A REPL session on `user` redefines `f`
  from `Int` to `String` and back, so `user.cl` is byte-identical again.
  The next cached launch crashes.
- **Signature.** SIGSEGV (exit 139) in `--run app.cl`, in the linked
  executable, and at `(g)` after `/mod app` in the REPL. `--no-cache --run`
  gives 41.
- **Seam.** The restored `lib.o`'s `g` loads `__cranelisp_got_user` at
  offset 0, which is slot 0. `user.meta.json` holds `f` at slot 2, with slots
  0 and 1 retired. The manifest records `user`'s hash for `lib`, and the hash
  is unchanged, so `lib` validates and restores.
- **Control.** The sibling project makes an ABI-preserving edit and revert
  instead (`(defn f [] 42)`, then `41`). `f` keeps slot 0, and every leg
  gives 41. An ABI-changing edit without a revert changes `user.cl`, which
  makes `lib` stale, and the call gives `"s"`.
- **Reach.** The hazard is wider than the filed "entry" framing. In the
  failing `--run` launch, `user` is a cache-restored dependency, not the
  entry, so P15's entry preload is not involved. Any module whose authored
  slots move during a REPL session, and whose text then returns to an
  earlier version, can trigger it. `/mod lib` alone masks the defect,
  because `/mod` recompiles the module it loads.

## Attribution

- **Mechanism: confirmed.** The sibling control differs only in whether the
  slot moves, and the seam shows the stale index. *Refuted if* a build that
  validates `lib` as stale, or relocates its call at `f`'s current slot,
  still crashes.
- **Entry point: design.** [int §7.6](../../design/int/int.md#76-dependency-record-and-validity)
  states that an importer's object embeds GOT slot indices. It keys the
  dependency record only by source hash. Under REPL ABI-changing increments
  ([session transaction §7.1](../../design/int/session-transaction.md#71-the-commit-gate-is-the-single-slot-policy-authority)),
  the slot layout is no longer a function of the source, and §8.2's faithful
  writes persist the moved layout under the old hash. The class is
  `artifact-underkey`, and the face is `null-got-slot`.
- **Owner: provisional.** `design`(int) places the correction, and `dev`
  builds it. The correction may change the persisted record and so the
  cache schema. It goes through `arch` if it touches
  `cranelisp-backend`'s cache manifest API.

## Open

- `test`: commit K-6 RED, with its sibling control.
- `design`(int): place the correction; `qa` then allocates `dev`'s unit row.
- `qa` keeps this action until the fix lands and K-6 is stamped.

## Resolved (qa, 2026-11-18, `2d3a5b3e`)

- **Correction:** a recorded member is keyed by its source hash with its
  authored slot layout (`3c4c0f7b`), with the backend's schema 34
  (`f3f9cc47`), the end of a stored layout at a `.meta` rewrite
  (`c53a3f4b`) and one decode shared by validation and restore
  (`2d3a5b3e`).
- **Evidence.** K-6,
  `tests/cache.rs::cache_restored_text_after_abi_change_preserves_importer_calls_across_modes`,
  was RED on the signal in `qa`'s runs through `7888c515` and passes in
  `qa`'s full run at `2d3a5b3e` with its control. The module rows are
  `cache::dependency_record::tests::slot_layout::*`.
- **Cost.** Four warm debug runs of `--run exemplar/tests.cl` took 0.89 to
  0.94 s, against 0.96 s before the change and 1.23 s with the first
  version of it.
- **Left:** `test` stamps K-6 `fixed=S124/3c4c0f7b`. This file stays until
  `sprints/SPRINT.md` and `sprints/ROADMAP.md` drop their links to it.

