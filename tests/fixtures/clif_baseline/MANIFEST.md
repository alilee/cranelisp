# L-B1 golden-CLIF corpus — MANIFEST

**Lane:** L-B1 (analysis-off differential oracle, byte-identical-off) —
`tests/plan/s100-ownership-verification.md` §3.1; corpus pins per the S102
/arch Q1 ruling (canonical home `design/arch/ownership-inference.md` §6.2).
**Owner:** `/qa` (corpus + this manifest); `/dev`(backend) executes the
capture (B0-be, `design/backend/ownership-codegen.md` §13.1) and commits the
golden dumps beside this file under `golden/`.

## Capture contract (binding on the B0-be capture change-set)

- **Mechanism:** `CRANELISP_CODEGEN_DUMP=*`, cold-cache `--run --no-cache`,
  one invocation per corpus entry in an isolated tmpdir (no prelude file —
  every entry is self-importing). Script: `tests/scripts/clif_golden.sh`.
  `--no-cache` (S102 Wave 3R, review F4) structurally eliminates the
  nice-worker `.o` cache-write pass, so each symbol dumps exactly ONCE —
  the JIT pass, which is what the goldens pinned (verified byte-identical
  13/13 at adoption, zero churn). A **duplicate frame is a hard error**
  (config drift — the cache pass leaked back in), never deduped.
- **Frames** sorted by `module::symbol` (Hook H1 frame-atomic writes;
  harness-side sort is the default resolution unless the dump interleaves
  mid-function — qa plan §6 G-1). **Zero frames extracted is a hard error**
  (the S102 Wave-1 empty-vs-empty false-green class, review F3) — the dump
  channel is STDERR (backend lib.rs).
- **Content byte-verbatim, NO canonicalization** — wrapper/slot identity is
  load-bearing (masking blinds the oracle to the 0483 class).
- **Determinism self-test:** double capture per entry, byte-identical,
  BEFORE any golden commit.
- **Config pins (enforced by `env -u` in the script's `dump()` and by
  `env_remove` in the in-suite smoke — keep the three sites in sync):**
  all emission-affecting env unset — `CRANELISP_NO_OWNERSHIP`,
  `CRANELISP_NO_LENIENT`, `CRANELISP_CAPTURE_BORROW`,
  `CRANELISP_NONATOMIC_RC`, `CRANELISP_RC_STATS`, `CRANELISP_RC_DEC_CHECK`
  (each gates CLIF emission — backend `heap.rs` / `sparkability.rs`), and
  `CRANELISP_NO_IO_SCHEDULE` (pre-typecheck bind-chain transform,
  `src/process_form.rs` — shapes the ParBind entries). Compile-time trace
  vars (`CRANELISP_RC_TRACE`, `CRANELISP_CODEGEN_TRACE`,
  `CRANELISP_GOT_TRACE`, `CRANELISP_MODULE_TRACE`,
  `CRANELISP_SCHEDULER_TRACE`, `CRANELISP_IO_TRACE`) are also cleared —
  they write to stderr, the dump channel. Worker-count flags absent;
  runtime-only knobs (`CRANELISP_SPARK_BUDGET`, `CRANELISP_SATURATION_GATE`,
  `CRANELISP_DEGREE`) do not affect CLIF and are unpinned; debug binary
  from a clean `cargo build`.
- **Green-only:** every entry runs green at capture time (verified at corpus
  authoring, 2026-07-03 — exit codes recorded below). Shapes under open
  failing-not-ignored guards are EXCLUDED — see `EXCLUSIONS.md`.
- **Extension ≠ re-baseline; scoped re-baseline only** for
  emission-affecting changes, delta attributed to the change's seam in the
  same commit (the `public-api.txt` discipline). Wholesale re-capture
  without attribution is forbidden.

## Entries

| # | Entry | Source fixture | Shape (mechanism surface) | Green witness (exit, 2026-07-03) | Capture SHA |
|---|---|---|---|---|---|
| 1 | 01_adt_construct_match | `corpus/01_adt_construct_match.cl` | ADT construct + match projections | 24 | `05818e9` |
| 2 | 02_closures_fn_as_value | `corpus/02_closures_fn_as_value.cl` | closures + same-module fn-as-value (1 instantiation) | 22 | `05818e9` |
| 3 | 03_auto_curry | `corpus/03_auto_curry.cl` | auto-curry partial application | 6 | `05818e9` |
| 4 | 04_vec_cow_loop | `corpus/04_vec_cow_loop.cl` | vec COW loop (push/set/get/len, direct calls) | 220 | `05818e9` |
| 5 | 05_string_externs | `corpus/05_string_externs.cl` | string externs (Decision-24 consuming; S5 sibling surface) | 6 | `05818e9` |
| 6 | 06_tco_loop | `corpus/06_tco_loop.cl` | TCO self-recursion (stack-slot back-edge surface) | 186 | `05818e9` |
| 7 | 07_trait_dispatch | `corpus/07_trait_dispatch.cl` | deftrait + impls + static dispatch | 8 | `05818e9` |
| 8 | 08_adt_in_vec_projection | `corpus/08_adt_in_vec_projection.cl` | ADT-in-Vec projection-read loop (I-G1 class) | 45 | `05818e9` |
| 9 | 09_parbind_launch | `corpus/09_parbind_launch.cl` | ParBind/LaunchContinue auto-spark D&C (R6 escape class) | 148 | `05818e9` |
| 10 | f1_machinery | `tests/fixtures/s99/f1_machinery.cl` | S99 F1 — spark machinery + shared-grid reads | s99_fixtures.rs guards | `05818e9` |
| 11 | f2_contention | `tests/fixtures/s99/f2_contention.cl` | S99 F2 — shared-Vec-of-ADTs copy contention | s99_fixtures.rs guards | `05818e9` |
| 12 | f3_inverted_search | `tests/fixtures/s99/f3_inverted_search.cl` | S99 F3 — inverted search | s99_fixtures.rs guards | `05818e9` |
| 13 | f4_sudoku | `tests/fixtures/s99/f4_sudoku.cl` | S99 F4 — copy-per-guess search | s99_fixtures.rs guards | `05818e9` |

The S99 entries (10–13) are referenced in place, not copied — their
parallel≡serial guards (`tests/s99_fixtures.rs`) are the green witness; the
capture runs them serially (`CRANELISP_NO_LENIENT=1` is NOT set — config
pins above apply; the dump is of compiled code, not execution order).

## Golden layout (written by the capture)

```
tests/fixtures/clif_baseline/golden/{entry}.clif   — sorted, byte-verbatim
```

The in-suite smoke (`tests/ownership_fences.rs::clif_golden_single_module_smoke`)
compares entry 06 (the smallest) against its golden on every canonical run —
RED until B0-be lands the capture; the full-corpus diff runs via
`tests/scripts/clif_golden.sh diff` at wave gates.

## Re-baselines (scoped, attributed — MANIFEST §"Extension ≠ re-baseline")

- **11 of 13 entries (01, 02, 03, 04, 05, 07, 08, f1, f2, f3, f4)** —
  re-captured S118 (FIXME 0908) for the **W3 consumer migration onto canonical
  drop glue**, change-set `2df95c41..966d298e` (emitting seam: `c6234398` S1,
  `emit_typed_rc_dec` becomes the canonical glue-call emitter; `22072a0c` S3
  per-arm match scrutinee lifetimes; `2ec5736d` S5+S6 the legacy-emitter
  deletion). **06_tco_loop and 09_parbind_launch are byte-identical** and were
  not rewritten. Three drift classes, all in the ownership family, certified
  frame-by-frame (per-frame program-opcode multisets compared modulo SSA/block/
  sig/fn renumbering — identical in 42 of 43 f4 frames and in every frame of
  the other ten entries):
  1. **release-site collapse** (the dominant class, all 11 entries): the inline
     guarded-dec sequence — `iadd_imm ptr,8; iconst 1; atomic_rmw sub; icmp eq;
     brif; fence` plus the inline `iconst 1024` nullary guard, the
     `DROP_GLUE_PTR` load at +24 / `func_addr` + embedded-glue call, and the
     terminal `dealloc` — becomes ONE `call fnN(ptr)` with `fnN = colocated
     u0:NN` at a **VOID `(i64)` signature**: the canonical per-concrete drop
     glue, whose body now owns the guard, the fence and the transitive
     teardown. Every collapsed chain is replaced by ≥1 glue call (verified
     mechanically per frame: fences lost ⇒ glue calls gained), so no release
     is silently dropped.
  2. **new release sites** where W3 plugged leaks — glue calls EXCEED the
     removed legacy releases in `f3::main` (+3 vs 2), `f4::is-solved-helper`
     (+5 vs 1) and others. Additive release work.
  3. **per-arm match scrutinee lifetimes** (`22072a0c`): four ADDED retains in
     f4 (`propagate` +1, `eliminate-from-peers-helper` +1,
     `propagate-pass-helper` +2), each a retain of the arm-bound payload paired
     with a per-arm release of the scrutinee box on the same path — where the
     golden leaked the box and let the payload live inside it. Retain counts are
     otherwise preserved in all 43 f4 frames and all other 12 entries.
  Determinism self-test 13/13 before write; an independent second capture
  reproduced all 13 files byte-identically; `clif_golden_lane_no_drift` green.
  **One hunk is a defect sighting, not a neutral reshape —
  `f4_sudoku::user::Grid.cells` drifted into a SHALLOWER release** (FIXME 0903,
  first censused family: synthetic accessor of a generic/undeclared-field
  product). Its self-param release did NOT migrate to canonical glue: the
  golden's transitive step (`load self+24`, 1024 guard, inner dec,
  `dealloc(inner)`) is GONE at HEAD with no glue call taking it over — the
  ONLY frame in either lane where a teardown level was lost (mechanically
  checked across all 48 drifted frames). Known, attributed, pre-existing-
  direction leak (0903's census: "both leak today"; plausibly a contributor to
  the 12,431 that cell #21 measures). **The blessed golden is NOT certification
  that the shallow release is correct.** When the S119 0903 ruling lands this
  frame is expected to drift again — that re-baseline is the fix's own witness
  (named in 0903's acceptance).

- **02_closures_fn_as_value, 08_adt_in_vec_projection, f1_machinery,
  f2_contention, f3_inverted_search, f4_sudoku** — re-captured S116 Wave 3
  after `6318fe87` added the canonical recursive drop-glue registry.
  **Function-ID numbering only; no instruction or control-flow change.** The
  registry proactively declares one exported glue function for each concrete
  owning return type before ordinary function compilation. Those declarations
  shift later module-local Cranelift `FuncId`s by the number of concrete glue
  functions in that module: +1 in entry 02, +3 in entry 08 and F1/F2, +4 in
  F3, and +8 in F4. Every observed hunk changes only a `colocated u0:N`
  operand; signatures, blocks, calls, RC operations, and all seven other
  entries are byte-identical. This is the intended registration consequence
  of Wave 3, not a consumer-emission change. The required double-capture
  determinism self-test passed 13/13 before recapture.

- **02_closures_fn_as_value, 07_trait_dispatch, f4_sudoku** — re-captured S115
  Wave 3b (FIXME 0753 / 0749). **Codegen change; ADDITIVE release work only, no
  RC op removed anywhere.** The moded-arg post-call dec
  (`apply.rs::emit_post_call_decs` — the release of a TEMPORARY argument passed
  into a `Borrowed` parameter) was a bare `heap::emit_rc_dec(.., None)`: an
  atomic dec plus a plain `dealloc`, which freed the temporary's own box and
  STRANDED everything the box owned. It now routes through the ONE type-directed
  release (`rc_emission::emit_typed_rc_dec`), so each drifted frame gains
  exactly the teardown its temporary's TYPE requires, inside the existing
  `rc == 0` branch:
  - **02_closures_fn_as_value** `user::main` — a CLOSURE-typed temporary: the
    free path now loads the box's embedded `DROP_GLUE_PTR` (+24), `call_indirect`s
    it when non-zero, then deallocs (three added blocks). Without it a curried /
    returned closure's own captures were never released.
  - **07_trait_dispatch** `user::main` — an ADT temporary: the free path now
    loads field 0 (+24), decs it, runs its teardown on `rc == 0`, then deallocs
    the box (two added blocks). This is the exact FIXME-0753 measurement —
    `(deftype G2 (Gr [cells])) (defn peek [g] 7) (defn main [] (Pure (peek (Gr
    [5 5]))))` was allocs=3 deallocs=2 analysis-ON and 3/3 analysis-OFF.
  - **f4_sudoku** `eliminate-from-peers` — a Vec temporary: `call dealloc(v)`
    becomes `call vec_drop(v, elem_dec_fn)`, which frees the elements and the
    data buffer, not just the Vec struct. `solve-range` — the nested case (an
    ADT temporary whose field is a Vec of ADTs): field dec → `vec_drop` with the
    element-dec fn pointer → dealloc.
  Everything else in the three diffs is mechanical `vN`/`blockN`/`sigN`/`fnN`
  renumbering behind the inserted blocks. The other 10 entries are
  byte-identical (`clif_golden.sh diff` clean across all 13 post-capture).
  Certified line-by-line: every hunk ADDS a release in the `rc == 0` path;
  none removes a dec, an inc, or a fence.

- **f4_sudoku** — re-captured S102 (fixture-driven, NON-codegen). Wave-A
  `c09c0a2` edited `tests/fixtures/s99/f4_sudoku.cl` to redefine→re-export the
  bootstrap-seeded `primitives/Option` instead of a local `deftype Option`, so
  the two user-module constructor frames `user::None`/`user::Some` (formerly
  emitted from the local ADT) are no longer user codegen — they come from the
  primitives bootstrap seed. Delta is EXACTLY those two frames dropped
  (45→43 frames); all 43 remaining frames are byte-identical to the `05818e9`
  batch. Not a codegen change; the golden was stale against the checked-in
  fixture. Verified `clif_golden.sh diff` empty across all 13 post-capture.

- **04_vec_cow_loop, 07_trait_dispatch, f3_inverted_search, f4_sudoku** —
  re-captured S102 increment I, ladder entry **B4** (the static allocation/RC-
  density admission axis on sparkability, `design/backend/lenient-eval.md` §2.7
  / `ownership-codegen.md` §13.4). **Codegen change, facts-present only.** With
  ownership facts present the density axis declines the allocation-dense heap-
  returning sparks in these four fixtures (facts-present declines: 04×1, 07×2,
  f3×3, f4×5), so each declined site emits its **sequential arm** instead of the
  lenient create-gate (spark) branch — the CLIF for the enclosing frame shrinks
  accordingly (e.g. `04::main` create-gate removed). The other 9 entries are
  byte-identical (`clif_golden.sh diff` clean across all 13 post-capture). The
  move is an **intended admission-set change**, not drift: it is exactly the
  scheduler-side decline B4 exists to make. **Toggle-off is byte-identical** —
  under `CRANELISP_NO_OWNERSHIP=1` the axis is inert (engaged=0 on all four),
  so the facts-absent codegen is unchanged; the golden here is the facts-PRESENT
  capture per the dump contract (§Capture contract unsets `NO_OWNERSHIP`).
  Determinism self-test passes 13/13.

- **12/13 entries (all but 06_tco_loop)** — re-captured S103 Wave-3c (`01464ba`),
  facts-present. **Two attributed causes, one codegen change:**
  1. **07_trait_dispatch = genuine ownership CHECK-ELISION.** With ownership
     facts present, a proven-unique/borrowed site drops its dynamic guard
     (`load + icmp + brif` → straight `jump`, the guard block removed), so the
     `07::*` frames shrink. Verified **toggle-reversible**: the guard is PRESENT
     under `CRANELISP_NO_OWNERSHIP=1` and ELIDED with facts on, both exit 8 —
     the byte-identical-off oracle holds (toggle-off golden unchanged; this
     golden is the facts-PRESENT capture per §Capture contract). Also carries
     the B4 density-decline already attributed above.
  2. **The other 11 entries (01/02/03/04/05/08/09 + f1/f2/f3/f4) = FuncId /
     GOT-offset SHUFFLE** from the Wave-3b (II-B2 reuse-token) function
     registration — the reuse-token runtime helpers (`runtime/reuse_hit` /
     `runtime/reuse_miss` catalog entries) register new FuncIds, shifting the
     numeric FuncId/GOT-slot operands baked into every frame's call sites. This
     is a **numbering shuffle, not a semantic codegen change** — the instruction
     structure of these 11 frames is otherwise unchanged. Not drift: it is the
     mechanical consequence of adding the reuse-token catalog helpers. **06_tco_loop
     is unchanged** (no calls to the shuffled helpers, no elision site).
  Behaviorally spot-checked before trusting the regen (all 9 corpus exits + 17
  s99 guards green); determinism self-test passes 13/13; `clif_golden.sh diff`
  clean post-capture.
