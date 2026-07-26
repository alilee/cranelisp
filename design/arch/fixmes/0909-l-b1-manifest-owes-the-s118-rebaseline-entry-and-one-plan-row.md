---
number: 0909
target: /qa
filed_by: /testing
filed_at: 2026-07-26
sprint_filed: 118
refers_to: tests/fixtures/clif_baseline/MANIFEST.md §Re-baselines;
  tests/plan/PLAN.md §S116-A (the §12.3.1 composed-application-residual row);
  tests/fixtures/clif_baseline/golden/f4_sudoku.clif (frame user::Grid.cells);
  design/arch/fixmes/0903-s4-1-frame-key-excludes-two-measured-escapee-families.md
status: open
---

# The L-B1 MANIFEST owes the S118 re-baseline entry, PLAN.md owes one row, and one drifted hunk is a 0903 sighting rather than a neutral reshape

FIXME 0908 (resolved in the same change-set as this filing) directed `/testing`
to re-capture both golden lanes. Three residues land in `/qa`-owned files.

## 1. `tests/fixtures/clif_baseline/MANIFEST.md` §Re-baselines — entry owed

The manifest is `/qa`-owned ("**Owner:** `/qa` (corpus + this manifest)") and
every prior re-baseline carries a documented, attributed entry there. The
change-set's commit body carries the full attribution; the manifest entry is
still owed. Paste-ready text:

> - **11 of 13 entries (01, 02, 03, 04, 05, 07, 08, f1, f2, f3, f4)** —
>   re-captured S118 (FIXME 0908) for the **W3 consumer migration onto canonical
>   drop glue**, change-set `2df95c41..966d298e` (emitting seam: `c6234398` S1,
>   `emit_typed_rc_dec` becomes the canonical glue-call emitter; `22072a0c` S3
>   per-arm match scrutinee lifetimes; `2ec5736d` S5+S6 the legacy-emitter
>   deletion). **06_tco_loop and 09_parbind_launch are byte-identical** and were
>   not rewritten. Three drift classes, all in the ownership family, certified
>   frame-by-frame (per-frame program-opcode multisets compared modulo SSA/block/
>   sig/fn renumbering — identical in 42 of 43 f4 frames and in every frame of
>   the other ten entries):
>   1. **release-site collapse** (the dominant class, all 11 entries): the inline
>      guarded-dec sequence — `iadd_imm ptr,8; iconst 1; atomic_rmw sub; icmp eq;
>      brif; fence` plus the inline `iconst 1024` nullary guard, the
>      `DROP_GLUE_PTR` load at +24 / `func_addr` + embedded-glue call, and the
>      terminal `dealloc` — becomes ONE `call fnN(ptr)` with `fnN = colocated
>      u0:NN` at a **VOID `(i64)` signature**: the canonical per-concrete drop
>      glue, whose body now owns the guard, the fence and the transitive
>      teardown. Every collapsed chain is replaced by ≥1 glue call (verified
>      mechanically per frame: fences lost ⇒ glue calls gained), so no release
>      is silently dropped.
>   2. **new release sites** where W3 plugged leaks — glue calls EXCEED the
>      removed legacy releases in `f3::main` (+3 vs 2), `f4::is-solved-helper`
>      (+5 vs 1) and others. Additive release work.
>   3. **per-arm match scrutinee lifetimes** (`22072a0c`): four ADDED retains in
>      f4 (`propagate` +1, `eliminate-from-peers-helper` +1,
>      `propagate-pass-helper` +2), each a retain of the arm-bound payload paired
>      with a per-arm release of the scrutinee box on the same path — where the
>      golden leaked the box and let the payload live inside it. Retain counts are
>      otherwise preserved in all 43 f4 frames and all other 12 entries.
>   Determinism self-test 13/13 before write; an independent second capture
>   reproduced all 13 files byte-identically; `clif_golden_lane_no_drift` green.
>   **One hunk is a defect sighting, not a neutral reshape — see item 3 below.**

## 2. `tests/plan/PLAN.md` — one row owed for the new warm-control leg

`/qa`'s §11.3 disposition asked for a warm-control guard leg beside cell #21. It
landed as `exemplar_ownership_residue_s116::warm_cache_hit_control_carries_no_ambient_residual`
(exact `residual == 0`, same scratch project / env / cold-then-warm sequence as
the subject, entry program imports `solver` but does no solve work). Suggested
row beside the existing §12.3.1 composed-application-residual row in §S116-A:

> | §12.3.1 warm cache-hit child carries no ambient compile-time residual (the premise of the absolute bound beside it) | `exemplar_ownership_residue_s116::warm_cache_hit_control_carries_no_ambient_residual` | positive control; `[S118]` authored GREEN (exact 0) |

## 3. FINDING — `f4_sudoku::user::Grid.cells` drifted into a SHALLOWER release

One frame's hunk is outside the reshape `/qa`'s §11.4 verification describes,
and the re-baseline has now blessed it, so it needs a record that outlives this
change-set.

`(deftype Grid [cells])` is an **undeclared-field product**, so `Grid.cells` is
exactly FIXME 0903's first censused family (synthetic accessor of a
generic/undeclared-field product; `emit_heap_binding_decs`'s type-keyed
non-concrete escape arm). Its self-param release did NOT migrate to canonical
glue. Instead:

- golden: `atomic_rmw sub; icmp; brif; fence;` → **transitive step** (`load
  self+24`, 1024 guard, inner dec, `dealloc(inner)`) → `dealloc(self)`;
- HEAD: the same inline guarded dec and fence, then `dealloc(self)` **with the
  transitive step gone** — the field is no longer released.

It is the ONLY frame in either lane where a teardown level was lost with no glue
call taking it over (mechanically checked across all 48 drifted frames). It is
in the release family, it is a known-and-attributed pre-existing-direction leak
(0903's census: "both leak today"), and it is plausibly a contributor to the
12,431 that cell #21 measures — `/qa` §11.3 already named `grid/Grid.cells` as
the lead. Two asks:

1. record it in the manifest entry (or here-by-reference) so the next reader of
   `f4_sudoku.clif` does not read the blessed golden as certification that the
   shallow release is correct;
2. when the S119 0903 ruling lands, expect this frame to drift again — that
   re-baseline is the fix's own witness, and it should be named in 0903's
   acceptance rather than discovered at the next wave gate.

## Proposed resolution

`/qa` pastes items 1 and 2 into its files, folds item 3's finding wherever it
belongs (manifest entry, 0903's acceptance list, or the S119 plan), then deletes
this file. Nothing here blocks the W8 gate: both golden lanes are green at HEAD
and the new control leg is green.
