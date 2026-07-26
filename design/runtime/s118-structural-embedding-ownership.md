# Sprint 118 — the structural-embedding ownership contract (FIXME 0835)

**Status:** W2b design of record — RULING. Implementation landed W2b
(`959833ea`); **§5's shared-tail negative cell amended post-landing** to the
unit-tier detector the profile can actually arm, with the general rule stated at
§5.1 (FIXME 0886, `/review`-filed, ruled by `/design`).
**Scope:** the runtime pair — producer `cranelisp-primitives::marshal`,
consumer/authority `cranelisp-intrinsics::drop`.
**Authority:** elaborates `design/arch/bounded-contexts.md` §4a (primitives) /
§4b (intrinsics); sibling of `design/runtime/s117-primitives-integrity.md`,
which established this directory as the home for a contract that spans the pair
rather than sitting inside one crate's interior.
**Inputs:** FIXME 0835 (+ the S118 `/qa` attribution ruling and the ambient
prelude-load scope note); `tests/slist_sconcat_ownership_0835.rs` (the committed
repros A + B); `tests/plan/s118-test-plan.md` §2.5 / §4.5;
`design/backend/transitive-drop-glue.md` §7.2 (the falsification recipe that
routed the defect here).

---

## 1. The question, and the answer

> For structural tail-embedding — `sconcat`'s `ys` case — **what does the
> producer owe?**

**Ruled: exactly one reference, on the node it stores. Nothing else.**
`consume_slist` is correct and does not change.

The two candidates the `/qa` ruling put up:

| Candidate | Disposition |
|---|---|
| **(a) head-only inc at the embed site** — producer-side fix in `cranelisp-primitives::marshal`; `consume_slist` untouched | **ACCEPTED** |
| **(b) any variant that changes consume semantics** (deep-consume, "descend past a live reference") | **REJECTED** |

(b) is rejected on three independent grounds, any one of which is sufficient:

1. **It ratifies the over-inc.** `/qa` ruled `consume_slist` correct
   tree-ownership drop glue (dec the node handed to you; descend only when that
   was the last reference). Making it deep would not fix a defect — it would
   redefine a correct consumer to compensate for a wrong producer, and the
   over-inc would become load-bearing.
2. **It breaks genuinely shared tails.** `sconcat`'s whole purpose is that the
   result *shares* `ys`. A deep consume releases references the embedding list
   never took, so releasing the result would tear down a tail the caller still
   holds. The committed control
   `slist_sconcat_ownership_0835::control_slist_built_without_sconcat_balances_green`
   is the standing fence against exactly this wrong fix, and the repro file's
   header says so in as many words.
3. **It is not local.** `consume_slist` is the funnel every recursive drop-glue
   leaf routes through (`drop.rs` module rustdoc; §5 A3 of
   `design/intrinsics/diagnostic-modes.md`). Changing its semantics changes
   every `SList` teardown in the language to fix one producer's arithmetic.

---

## 2. The invariant, stated declaratively

Two rules, a producer rule and its consumer dual. Both are written for an
invariant table; both are auditable by reading a single function.

> **RE-1 — Structural embedding takes exactly one reference.** When a runtime
> helper embeds an existing heap structure into a new structure **by pointer**
> (structural sharing, not copying), it takes exactly **one** `rc_inc` — on the
> node it stores — and no others. Interior nodes are owned by their parent
> node; elements are owned by the node that holds them. Those owners are
> unchanged by the embedding and MUST NOT be re-counted.
>
> **Corollary (the auditable form):** the number of incs a producer performs
> for one embed is **1, independent of the size and the depth of the embedded
> structure**. A producer whose inc count scales with `|structure|` is by
> construction minting references no owner holds.

> **RE-2 — `consume_*` are tree-ownership drop glue, and stay so.** Every
> `consume_*` in `cranelisp-intrinsics::drop` releases exactly the one
> reference handed to it and descends only when that was the last one. It is
> therefore structurally incapable of discharging a reference no owner holds.
> RE-1 is not a convention the consumer could be relaxed to tolerate — it is
> the *only* producer discipline this consumer can be paired with.

> **RE-3 — copy and share are different producer choices with different
> reference rules, and the choice is per-field.** *Copied* content takes one
> inc per copied reference (`sconcat`'s `xs` items, each stored into a fresh
> `SCons`: correct today). *Shared* content takes one inc on the shared node
> (RE-1). *Deep-copied* content takes incs only on the leaves it re-uses
> (`quote_sexp_build`'s `TAG_SEXP_STR` / `TAG_SEXP_SYM` arms, which re-use the
> `String` pointer and inc it once: correct today). RE-3 is what makes the
> whole of `marshal.rs` auditable against one rule instead of three.

### 2.1 Why the defect is exactly an RE-1 violation

`marshal::deep_rc_inc_slist` walks the whole `ys` chain and incs **every node
and every element**. For an `n`-cell `ys` holding `h` heap-typed elements it
performs `n + h` incs where RE-1 licenses **1**. The surplus is

```
over-incs  =  (n − 1) interior nodes  +  h heap-typed elements
```

— references no structural owner corresponds to, and (RE-2) undischargeable by
any release: the caller's release of `ys` stops at the head, and the result's
release stops at the same head. Per-call, and linear in `|ys|` at constant type
depth. That is `/qa`'s measured signature (+3 / +7 / +6) reproduced from the
code, and it is why the transitive-discharge (backend-glue) hypothesis — whose
residual would track type *depth* — was falsified.

The allocation residual the repros measure is **bounded by and linear in** the
over-inc count, not identical to it (an element pinned by its own surplus
reference may also sit under a node pinned by a different one, and teardown
stops at the first node that is not on its last reference). The ruling does not
rest on the exact projection; it rests on RE-1, which the code violates
literally.

### 2.2 Why the existing unit row is green — the coverage miss, precisely

`crates/cranelisp-primitives/src/marshal/tests.rs::decision24_sconcat_rc_balanced`
asserts exact alloc/dealloc balance over `sconcat` and passes at HEAD. It is
not wrong; it is *blind*, and the reason is arithmetic:

- its `ys` is a **one-cell** list (`n = 1` ⇒ zero interior nodes), and
- its elements are **bare nullary tags** (`h = 0` ⇒ `rc_inc` no-ops).

`over-incs = (1−1) + 0 = 0`. The single row in the suite that exercises this
seam sits exactly on the one point where the defect is invisible. The two
missing axes are `|ys| ≥ 2` and heap-typed elements — the
`tests/CLAUDE.md` §"Coverage by definition variants" lens applied to a producer
seam. §5's matrix restores both.

---

## 3. The change — exact seams

Both seams are in **`crates/cranelisp-primitives/src/marshal.rs`**. Nothing in
`cranelisp-intrinsics` changes.

| # | Seam | Change |
|---|---|---|
| S1 | `sconcat`, `items.is_empty()` branch (`marshal.rs`, the `deep_rc_inc_slist(ys); ys` arm) | replace the deep walk with **one** nullary-safe inc on `ys` (`shallow_rc_inc`, which already routes to the blessed `cranelisp_intrinsics::rc::rc_inc` and carries the nullary-tag skip) |
| S2 | `sconcat`, non-empty branch (`deep_rc_inc_slist(ys)` before the build loop) | same — one inc on `ys` |
| S3 | `fn deep_rc_inc_slist` | **DELETE.** Its only two call sites are S1/S2 |
| S4 | `sconcat`'s rustdoc "**RC ownership**" paragraph | it currently documents the defect as intent ("It gets a deep RC inc (every SCons node and every element)"). Rewrite to state RE-1 for the `ys` case and RE-3 for the `xs` case. Principle 26 — the record follows the settled state, in the same change-set |

**The two `consume_slist` calls at the end of `sconcat` STAY, unconditional.**
The inc/consume pair is not redundant ceremony:

- It keeps the Decision-24 epilogue (`consume_slist(xs); consume_slist(ys);`)
  **uniform** with every sibling complex-heap extern (`quote_sexp`, `str_join`,
  `cranelisp_run_io`). Making `sconcat` the one extern with a conditional or
  absent consume is precisely the divergent-sibling shape this project is
  eliminating (Principle 7; `tests/CLAUDE.md` §"Coverage by definition
  variants").
- It states the reference taken **locally and explicitly** at the embed site,
  rather than encoding it in a non-local pairing of two deletions that a future
  edit can silently break (Principle 18 — enforce invariants structurally;
  Principle 26).
- It is a strict **reduction** in atomic traffic, not an addition: `2` RMWs per
  call replacing `2|ys| + 2`.

**Rejected mechanism alternatives**, recorded so they are not re-proposed:

- *Move instead of inc-then-consume* (delete the inc **and** `consume_slist(ys)`).
  Arithmetically correct today, but it makes the epilogue non-uniform and makes
  correctness depend on "no future early-return path exists in this function".
  Rejected on Principle 18.
- *A general `embed_shared_tail`/`embed_structure` API in intrinsics.* One
  caller, one line of body, and it would put a producer-side rule behind a
  consumer-side crate boundary. Rejected on Principles 6 and 8.
- *Deep-consume* — §1, three grounds.

**No public-surface delta.** `deep_rc_inc_slist` and `shallow_rc_inc` are
private; `sconcat` is `pub(crate)` behind an unchanged extern symbol. No
`crates/cranelisp-primitives/public-api.txt` change, no `cranelisp-types`
change, no `CACHE_SCHEMA_VERSION` bump, no catalog/ABI/heap-layout change, no
`/arch` gate.

---

## 4. The abort face — what reading establishes, and what it does not

**Established by reading:** the over-inc alone **cannot** produce the glibc
abort.

1. An extra reference is **monotone in the safe direction**: it can only delay
   a free, never advance one. Every free in this seam is reached only through
   `atomic_dec_rc` / `consume_shallow` returning `old_rc == 1`, and every dec is
   paired with a reference that was actually taken. So RE-1 violations produce
   **leaks**, never a premature free and never an out-of-bounds write.
2. `free(): chunks in smallbin corrupted` and `corrupted double-linked list`
   are produced by a **write into a freed chunk** or a **double free** — not by
   leaks.

Therefore the abort face requires a **second ingredient**, and the honest
ruling is that reading `sconcat` / `deep_rc_inc_slist` / `consume_slist` does
not identify it. Two candidates survive reading; they make **opposite
predictions**, which is what makes the measurement worth taking *before* the
fix lands.

**Candidate (i) — a co-present premature-free defect that the leak masks.**
Evidence: FIXME 0835's own controls (the same logical computation with
`` `true `` survives to 6 cells where `(SexpBool true)` dies; reshapes move the
failure between silent exit, expansion panic and hang without moving the arity
ceiling — the signature *of* corruption, not of this arithmetic). The nearest
open premature-free family is **FIXME 0810 Face B / 0782** — release of an
owned scrutinee under a constructor pattern taking the extracted payload with
it — and that is *literally* the shape every repro-A cell runs:
`(match xs [(SCons h t) (sfold f (f acc h) t) SNil acc])`.

> **Consequence /dev must be warned about:** under candidate (i) the surplus
> interior references are currently **masking** the premature free (they keep
> the extracted tail alive). Removing them can make the abort face *more*
> frequent, not less. A repro-A cell that stays RED — or a new abort elsewhere
> — after the fix is therefore an **expected possible outcome**, not evidence
> the fix was wrong. The fix stands on RE-1 and on repro B either way.

**Candidate (ii) — the deep walk is itself the wild write.** `deep_rc_inc_slist`
is the only code in this seam that dereferences nodes **the caller did not hand
it**: it reads `FIELD0`/`FIELD1` of every interior cell and calls `rc_inc` on
whatever it finds. If any tail cell holds a value that is not a live `SList`
node — a stale node, an interior address, or a scalar above
`NULLARY_TAG_THRESHOLD` — `rc_inc` performs a `fetch_add` at `addr + 8`: a write
into arbitrary or freed memory, which is exactly the smallbin / double-linked-list
signature. Under (ii) the head-only fix **removes the walk entirely** and the
abort face closes with the same one-line change.

### 4.1 Detector-pointing plan (what the W2a-proven kit is aimed at)

`/dev` executes D0–D2 **before** writing the fix — they are cheap, and the
pre-fix state is unrecoverable afterwards. All arming is per-child
`Command` + `env_clear` + enumerated allow-list
(`design/intrinsics/diagnostic-modes.md` §7.1 arming discipline, §7.6 harness);
nothing is armed at suite scope.

| # | Detector | Pointed at | What it discriminates |
|---|---|---|---|
| **D0** | none — `--run` vs REPL at the **same shape** | the 6-cell shape: `repro_b_chained_sconcat_residual_does_not_grow_per_call`'s three-call leg (`--run`) vs `repro_a_top_level_six_cell_slist_teardown_does_not_abort` (REPL) | if `--run` completes while the REPL twin aborts at the identical shape, the second ingredient is **mode-divergent** (session/thunk teardown) ⇒ candidate (i). If both abort, it is mode-independent ⇒ candidate (ii). Two runs |
| **D1** | `CRANELISP_RC_DEC_CHECK` armed (the §7.5 `seam_precheck` at `rc_inc`, `consume_shallow`, `atomic_dec_rc`) | both repro-A children | under (ii) the deep walk's `rc_inc` on a stale/interior pointer is **rejected at the seam** with `[CRANELISP RC/ALLOC SEAM VIOLATION] … rc_inc …` naming the pointer — a located answer instead of a glibc abort. Highest-value single measurement; available at HEAD |
| **D2** | **M1** quarantine (no reuse after free) | both repro-A children | if the abort survives M1, no freed chunk was reused ⇒ the corruption is not a UAF-write into recycled memory. If it disappears, it is, and D3 localizes it |
| **D3** | **M2** scrub-freed poisoning **+ D1 armed together** | whichever child D2 implicates | a stale read yields the poison word and the precheck rejects it at the seam that touched it — and **the seam name is the discriminator**: `rc_inc` names the marshal walk (ii); `atomic_dec_rc (drop glue)` reached from backend-emitted glue names the match/scrutinee family (i) |
| **D4** | **M3** paired alloc/free hard-check | the repro-B children, **after** the fix | the exactness leg for the leak face — makes an imbalance abort at the seam instead of surfacing at atexit |

Whatever D0–D3 return is recorded verbatim in the W2b outcome block. If they
localize the abort outside this seam, that is `/qa`'s new attribution question
per the FIXME's honesty caveat — **never** a re-open of the migrated backend
Track-B seams.

---

## 5. Unit matrix (`/dev`-owned)

`#[cfg(test)]` beside each seam, per the crates' externalized-`tests.rs`
convention. Rows marked **(RED first)** must be written and observed failing
*before* the fix (root `CLAUDE.md` §Testing; `sprints/METHOD.md` §2.2).

| Submodule | Normal / positive | Complexity / edge | Negative / fence |
|---|---|---|---|
| `marshal::sconcat` — the embed rule | **(RED first)** `xs` non-empty, `ys` = 2-cell with **heap-typed** elements: exact alloc/dealloc balance after the caller releases the result. This is `decision24_sconcat_rc_balanced` widened off its blind point (§2.2) | **(RED first)** `\|ys\|` ∈ {4, 8} with heap elements: residual 0 and **independent of `\|ys\|`** — the *rate* property, the unit-tier twin of repro B4; plus a `ys` whose element is a nested `SexpList` (a `Sexp` holding an `SList`) — inc count must not move with depth either | **(RED first)** **inc-count fence**: the embed performs exactly **one** inc for any `\|ys\|`, asserted against the RC counters, not by inspection. A deep-inc regression fails this row even if some future accounting change re-balances the totals |
| `marshal::sconcat` — shared tail | `ys` still live at the caller after the call: the tail is not torn down by the result's release; the two releases together balance exactly | **`ys` aliases a suffix of `xs`** (`sconcat xs <tail-of-xs>`): exact balance, and the result reads correctly after both consumes. This is the case the head inc is load-bearing for | releasing the result MUST NOT free a tail the caller still holds — after the result is consumed, assert `rc_of(ys) == 1` and read the tail's elements back, then `consume_slist(ys)` and assert the pair balances. The **unit-tier** detector for a premature free is the double-free assert in `alloc::dealloc`, which that second consume trips; **M1 quarantine belongs to the e2e/child tier** (§5.1) |
| `marshal::sconcat` — empty / nullary | `xs = SNil` (the `items.is_empty()` branch: result **is** `ys`) balances | `ys = SNil`; `xs` non-empty with `ys = SNil`; both `SNil` | `xs = SNil, ys = SNil` touches the heap **zero** times (alloc-counter delta 0) |
| `marshal::quote_sexp` — the sibling producer | existing deep-copy rows unchanged | `SexpSym` / `SexpStr` string re-use takes exactly one inc (RE-3); nested `SexpList` recursion | **grep-zero**: no producer in `marshal.rs` performs an inc whose count scales with the size of a structure it embeds. `deep_rc_inc_slist` is deleted and has no successor |
| `intrinsics::drop::consume_slist` | **behaviour unchanged** — the fix must not touch it; the existing rows are the invariance pin | multi-referenced interior node: the walk stops at the first node that is not on its last reference | **RE-2 fence**: build `a = [x, y]`, `b = SCons(z, a)`, release `b`, assert `a` still reads. A change that makes `consume_slist` descend past a live reference fails here |

### 5.1 A unit row cannot be "under M1 quarantine" — the substitute is the design (FIXME 0886)

The shared-tail negative cell as first written asked for the read-back to run
**under M1 quarantine**, so that a premature free would be a detector hit rather
than a silent correct-looking read. That is **not available to an in-crate unit
row**, and the constraint is structural, not incidental:

- M1 is armed per-child through the environment
  (`design/intrinsics/diagnostic-modes.md` §7.1), and the suite's own
  arming-discipline gate
  (`tests/detector_arming_discipline_guard.rs::no_test_sets_a_cranelisp_variable_in_its_own_process`)
  forbids a test arming a detector in its own process. `set_var` against an
  already-forced `LazyLock` is a silent no-op that reads green forever — the
  failure mode the gate exists to prevent (`crates/cranelisp-primitives/CLAUDE.md`
  §"Counting RC ops in a unit test").

**Ruled (`/design`, S118 post-W2b): the committed row's substitute IS the design
of record.** `crates/cranelisp-primitives/src/marshal/tests.rs::
re1_shared_tail_survives_the_results_release` reaches the same *question* with
the mechanism the unit profile actually has — the `rc_of(ys) == 1` read and the
element read-back establish the tail is intact, and the caller's own
`consume_slist(ys)` afterwards makes a premature free trip the double-free
assert in `alloc::dealloc`. The detector is loud and in-process; what changes is
which detector, not what is asserted.

**A child-harness variant of this row is NOT wanted.** It would be new
`/testing` scope for no additional discrimination: the M1 leg would prove the
same proposition the double-free assert already proves at this seam, and the
e2e/child tier already carries the armed coverage for this defect
(`tests/slist_sconcat_ownership_0835.rs` plus the §9.2-style armed acceptance
legs). The general rule this instance settles, for every future row in these
runtime-pair matrices:

> **Name the tier's own detector.** A unit-tier negative cell specifies an
> in-process mechanism (double-free assert, RC read, alloc/dealloc balance); an
> armed-detector (M1/M2/M3) expectation may only be written into an e2e or
> child-process row. A matrix cell that names a detector its tier cannot arm is
> a defect in the matrix.

**e2e need — assessed before the fix, and already satisfied.** The five REDs in
`tests/slist_sconcat_ownership_0835.rs` are the e2e tier for both faces, plus
the prelude-face cell `/testing` lands in this same change-set (§6.3). `/dev`
writes **no** new e2e.

---

## 6. Acceptance

### 6.1 The repros

All five REDs in `tests/slist_sconcat_ownership_0835.rs` flip GREEN
(`repro_b_single_sconcat_tail_embed_balances`,
`repro_b_chained_sconcat_residual_does_not_grow_per_call`,
`repro_b_longer_embedded_tail_balances`,
`repro_a_slist_teardown_on_the_test_runner_path_does_not_abort`,
`repro_a_top_level_six_cell_slist_teardown_does_not_abort`), and both controls
stay GREEN. The repro-A pair is subject to §4's candidate-(i) caveat; the
repro-B triple is not — it is the leak face and it is exactly what RE-1 fixes.

### 6.2 The binding W2b prediction — the P4 probe

**Re-run the P4 probe shape** (`tests/plan/s118-test-plan.md` §2.5): trivial
`Int`-returning child, **full stdlib** prelude (`CRANELISP_LIB=stdlib/`),
`--run --no-cache`, `CRANELISP_RC_STATS=1`, fresh tempdir, controlled env, HEAD
debug binary. **`1143 → 0`.** This is Branch H, and it is binding: a surviving
residual is a NEW attribution routed to `/qa`, never a silent re-scope.

Take the P3 shape (two tiny modules, one macro invocation, `+2`) at the same
time — it is the minimal deterministic form of the same face and the number
`/testing`'s cell fences.

### 6.3 The prelude-face cell

`/testing` lands ONE prelude-face exact-balance cell **in this change-set**
(plan §2.5 directive): trivial program + macro-invoking mini-prelude fixture,
exact balance. It is the standing fence for the ambient face, which has no
committed cell today.

### 6.4 Baseline flip accounting (plan §2.5, Branch H)

Cells **#10** (`ms_p8_conj_leak::int_loop_control_balances_green`), **#19**
(`conj_loop_does_not_leak`), **#20** (`conj_loop_parity_no_abort`) and **#23**
(`intrinsics_m3_detection_s116::m3_parity_clean_child_exits_normally_control`)
flip **at W2b** — their REDs are entirely the ambient term. **#21**
(`exemplar_ownership_residue_s116::…`) loses the 1143 ambient term here and
flips only after **W2b + W3**. A flip of any of these in W2a, W3-alone or W4 is
the S98 perturbation flag and re-opens attribution.

### 6.5 Armed-lane re-demonstration

The W2a detector proofs re-run unchanged (the A-row triplets, the two committed
M3 e2e cells, and `clean_heap_workload_balances_at_every_seam`) — the fix must
not perturb the armed lane. **Additionally** re-run the repro-B children once
with `CRANELISP_RC_DEC_CHECK` armed (per-child `env_clear`): a clean armed run
is the acceptance, not merely a balanced unarmed one.

### 6.6 Fail-on-revert

Every §5 row marked **(RED first)** carries a recorded fail-on-revert
observation. A row that passes with the fix reverted is not a guard.

---

## 7. Branch-F contingency

If the P4 residual **survives** W2b:

1. **The fix still stands, unchanged.** It is correct against RE-1 and is
   independently pinned by repro B and by the §5 unit matrix. It is not
   rolled back, re-scoped, or made conditional.
2. **The remainder returns to `/qa` as a distinct defect** — a new attribution
   with the surviving measurement as its evidence base and the P3 shape as the
   committed reduction `/testing` lands with it (plan §2.5 Branch F).
3. **The sprint owes the user a scope decision.** Cells #10/#19/#20/#21/#23
   then have no scoped flip track and are not in the §1 pre-authorized carry
   list.

The same contingency shape applies independently to the **abort face**: if
repro B flips and repro A does not, that is `/qa`'s new attribution question
per FIXME 0835's honesty caveat, carrying the §4.1 D0–D3 detector output as its
localization evidence — and my prior, recorded here so it can be checked, is
the FIXME 0810 Face B / 0782 match-owned-scrutinee seam that every repro-A cell
exercises through `sfold`.

---

## 8. Quality attributes

| Attribute | This ruling |
|---|---|
| **Simplicity** (P6) | The fix deletes a function and replaces two calls with two one-line calls. No new API, no new mode, no new carrier. Atomic traffic per call drops from `2\|ys\| + 2` to `2` |
| **Maintainability** | RE-1's corollary — "the inc count for an embed is 1, whatever the structure" — is checkable by reading one function and is asserted by a counter-based unit row, so the class cannot silently return |
| **Observability** | Unchanged by design (`marshal.rs` carries no diagnostics — primitives invariant 12). The observation surface for this defect is the intrinsics detector kit, pointed at it by §4.1 rather than instrumented into the producer |
| **Concurrency-safety** | Improved incidentally: `shallow_rc_inc` already routes to the blessed atomic `rc::rc_inc` (audit MED-1 / `rc-inc-entry-point.md`), and the fix removes `2(\|ys\|−1)` atomic RMWs from a path a spark can reach |
| **Performance** | Macro expansion is the hot consumer (the ambient face is `+2` per invocation, `1143` across a full stdlib prelude load). The fix is a strict reduction in both allocations retained and atomics executed |
| **Testability** (P5) | The seam is unit-testable in-crate against the alloc/RC counters with no session, no JIT and no subprocess; §5's inc-count fence tests the *rule*, not a symptom |

---

## 9. Cross-references

- `design/arch/fixmes/0835-slist-sexp-construction-corrupts-the-heap-at-small-sizes.md`
  — the defect record and the `/qa` attribution + prelude-face scope note.
  Stays **open** until implementation lands.
- `tests/slist_sconcat_ownership_0835.rs` — the committed repros and controls.
- `tests/plan/s118-test-plan.md` §2.5 (ambient face, Branches F/H, flip
  accounting), §4.5 (the attribution evidence table).
- `design/intrinsics/diagnostic-modes.md` §5 (A1–A4 seam asserts), §7.1 (arming
  discipline), §7.5 (`seam_precheck`), §7.6 (child harness), §3 (M1/M2/M3) —
  the detector kit §4.1 points.
- `design/primitives/primitives.md` §4 invariant 13 — RE-1 in the primitives
  invariant table.
- `design/backend/transitive-drop-glue.md` §7.2 — the falsification recipe that
  routed this defect out of backend; slice S2 is removed from the backend wave.
- `design/intrinsics/rc-inc-entry-point.md` — `rc::rc_inc` is the blessed inc
  entry point and carries the nullary-tag skip the fix relies on.
- `crates/cranelisp-primitives/src/marshal.rs` (S1–S4);
  `crates/cranelisp-intrinsics/src/drop.rs::consume_slist` (**unchanged**;
  RE-2's subject).

## Next skills

- `/dev` — narrow to the **runtime pair** (`cranelisp-primitives` +
  `cranelisp-intrinsics`). Order: §4.1 D0–D2 measurements → §5 RED-first unit
  rows → S1–S4 → §6.2 P4 probe → §6.5 armed re-demonstration.
- `/testing` — the §6.3 prelude-face cell, in the same change-set.
- `/qa` — only on Branch F, or if the abort face survives (§7).
