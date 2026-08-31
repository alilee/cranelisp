# S120 QA evidence delta — FIXME 0917 provenance correction

**Authority:** `qa`. Scope is `sprints/SPRINT.md` §Approved scope (0917 only);
the governing ruling is `design/backend/non-concrete-release-contract.md`
§6.2–§6.5 with `design/backend/transitive-drop-glue.md` §5.1's four-point
lattice reference. This document allocates evidence for the bounded
correction; it implements nothing and restates no standing plan
(`tests/plan/PLAN.md` rows for §12.3.1 and `tests/plan/s119-test-plan.md`
§5.3 remain the durable carriers they already are).
**Authority direction (user ruling, 2026-08-31, recorded in
`sprints/SPRINT.md` §Evidence log):** the correction is **authorized** by the
runtime requirement (`spec/12-runtime.md` §12.3.1 req. 1;
`spec/appendix-c-nfr.md` §C.1.1) and **shaped** by the approved backend
design (§6.2–§6.5). It is **accepted** by compiler evidence only: the reduced
0917 run/link cells, the backend module invariants, and the reduced-corpus
golden entries. The Sudoku exemplar, its threshold cell, and exemplar-derived
golden CLIF (`f4_sudoku`) **observe downstream consequences only** — they do
not authorize, shape, or block the correction, and no gate in this plan keys
on them. This supersedes the prior revision's B-1, which inverted that
direction (§7).
**Measured basis:** working-tree full suite 5,692 run / 5,672 passed /
20 failed / 1 skipped (2026-08-30, zero compiler-source change at that
checkpoint); focused pre-change RED 2026-08-31 —
`cargo nextest run --test nullary_arm_beside_boxed_arm_0917` 0 passed /
2 failed, both pairs exact marginal residual **4,402**; **re-confirmed by
`qa` on the post-handoff tree** (2026-08-31, after `test`'s comment-only
repro edits and the prepared corpus input): 0 passed / 2 failed, both pairs
exact 4,402, control absolutely balanced 4406/4406.

**Final measured basis:** the focused run/link pair is 2/2 GREEN at exact
marginal zero; the backend module tier is 533/533; the named provenance/UAF
fences are 42/42; and the full suite is 5,698 run / 5,680 passed / 18 failed /
1 skipped. The 18 failures are the 17 traced compiler carries plus the golden
lane's untouched downstream `f4_sudoku` drift. Reduced entries 01–10 and
f1–f3 match; entry 10 was captured twice byte-identically (11 frames, 731
lines, SHA-256
`38c1a0083405841f51e1699da36fc1fdb75a6bea392124f016cd3ba7a570d7c6`).
No existing golden was changed.

## 1. The changed condition, and the adequacy ruling on existing evidence

One product condition changes, and it is already stated and already RED:

> A match mixing a nullary-constructor arm with a boxed arm releases its
> loop's garbage exactly as the all-boxed control does (spec
> `spec/12-runtime.md` §12.3.1 req. 1; `spec/appendix-c-nfr.md` §C.1.1
> deterministic deallocation, and the nullary-ctors-MUST-NOT-allocate row).
> Evidence: `tests/nullary_arm_beside_boxed_arm_0917.rs` ×2 (`--run
> --no-cache`, `--link`), `assert_balanced` = exact marginal 0.

**Adequacy: the existing independent evidence is adequate; no duplicate e2e
condition is added.** One compiler-focused emission condition is added (§2
D5, §3.2) because the ruling removed the exemplar-derived frame from the
acceptance chain and the reduced golden corpus contains no frame exercising
the corrected class. Disposition of the three Wave-0 leads:

1. **"The control is absolutely balanced" — not a defect; it strengthens the
   pair.** The cells are free-standing (`(import [primitives [*]])`, no
   prelude), so the ambient compile-time term the marginal discipline exists
   to cancel (`tests/CLAUDE.md` §"Allocator balance is measured MARGINALLY")
   is measured zero here — the control's absolute 406/406 and 4406/4406 is
   the executed proof of that premise. The marginal therefore degenerates to
   the subject's absolute residual **with no slack**. The pair form is still
   load-bearing: the one-token subject/control axis (the arms' returned
   constructors) is the discriminating control that pins the *mechanism*
   (nullary-arm presence), per the control discipline.
2. **"The spec-side trace band does not name them" — correct today, repaired
   at Wave 4.** An annotation naming a failing guard would claim coverage
   that does not hold. Allocated, not performed: after the flip, `qa` extends
   the `spec/12-runtime.md` §12.3.1 requirement-1 band with
   `tests/nullary_arm_beside_boxed_arm_0917::nullary_arm_beside_boxed_arm_frees_its_loop_under_run`
   (one citation; the `--link` face and the exemplar cell remain test-side
   backlinks). The band is `qa`'s to edit in place, no filing cycle.
3. **"Three `// defect:` comments name `fn_compiler.rs::protect_return_value`"
   — a stale-record defect, owner `test`.** The method is defined at
   `crates/cranelisp-backend/src/compiler/rc_emission.rs::protect_return_value`
   (in `impl FnCompiler`), and FIXME 0917's header records the `git log -S`
   proof it was **never** in `fn_compiler.rs`. A token that was never true is
   a factual correction, not a locus move. **Discharged (S120 W1):** `test`
   corrected all three `// defect:` loci in-tree with the one prose clause
   each (`qa` verified the diffs), and `qa` repaired the same stale token's
   four occurrences in its own `tests/plan/s118-test-plan.md`
   (§11.8.1 ×3 including the braced attribution set, §11.8.6 item 1's
   `// defect:` template) with a correction note, so the wrong locus cannot
   be re-authored from either surface.

## 2. Delta by changed surface

Per the compact-correction form: condition / plausible wrong outcome / lowest
discriminating layer / existing evidence extended / limit.

| # | Changed condition | Plausible wrong outcome it must discriminate | Lowest layer | Extends | Limit |
|---|---|---|---|---|---|
| D1 | `ValueProvenance` gains bottom `NoReference`; nullary-ctor `Var`, `Apply` of a zero-field ctor, fieldless `ConstrADT`, scalar literals classify there; `Match` fold seeds at `NoReference`; arm-less match stays ⊤ | **UAF direction (the one that can crash):** `NoReference`/`Fresh` over-assigned to a reference-carrying value — a ctor **with** fields referenced as a value, or a wrapper kind claiming freshness — elides a protect the scope cleanup then consumes | backend unit (`fn_compiler.rs::value_provenance` matrix, contract §9 row 4) | the FIXME-0781 cells beside `value_provenance`; e2e negative fences `tests/false_fresh_provenance_residual.rs` and `tests/vec_assoc_param_mutate_return_uaf.rs` **stay GREEN** | classification only — proves nothing about which consumer reads it (D5) |
| D2 | Both thresholds restated: `is_fresh_construction` = `<= Fresh`; `yields_owned_temporary` = `matches!(p, Fresh \| OwnedTemporary)` | threshold left at `!= NotOwnedHere`, so a bare tag reads as an owned temporary at the release gates; or the seed left at `Fresh`, so an all-nullary match reads a false `Fresh` where an arm-less match must stay ⊤ | backend unit (both consumer thresholds pinned — sprint acceptance item 3) | `owned_temporary_threshold_separates_bindings_from_temporaries`, `the_two_thresholds_differ_exactly_at_a_general_apply` | inert-by-category-gate reasoning is design's (§6.2.2), not provable at this layer |
| D3 | Probe widens to the three-state classification, produced by the ONE `ctor_meta_at` keyed read, agreeing with `crates/cranelisp-backend/src/compiler/literals.rs::nullary_constructor_tag` | a second probe or second field-list read disagrees with the bare-tag lowering — the 0917 shape re-created one level down | backend unit (contract §9 probe row) + structural (no second read exists) | `trace_codegen` `ctor_meta_at_keyed_read_hits_real_def_and_misses_are_loud` | agreement is asserted over exercised references; absence-of-second-read is code shape, checked by `review` |
| D4 | Monotonicity pin replaces `provenance_owned_threshold_is_probe_independent` (equality cannot survive) | the pin is vacuous — no corpus node the probe moves, so an instrument indistinguishable from one that cannot fire | backend unit, **with detection proof in the same change-set**: strict descent asserted on the two moved shapes (bare nullary-ctor `Var`; mixed nullary/boxed match) AND no movement **across the owned/not-owned threshold** on the retained eight-node corpus (the negative leg — the deleted pin's surviving safety content; the probe may still refine within the owned side, as it already did pre-0917 on the retained ctor `Apply`, `OwnedTemporary → Fresh`) | the existing pin's corpus | proves the probe's direction, not the consumers' behaviour |
| D5 | Emission: the constructor half reaches exactly one consumer (`rc_emission.rs::protect_return_value`) and its whole content is **eliding** the unbalanced protect-inc — no compensating dec, no new licence arm; the scalar half is emission-neutral (§6.4) | (a) the fix balances by a compensating dec instead of eliding the inc — marginal 0 either way, so D6 cannot see it; (b) a scalar-typed frame drifts — §6.2.2's named falsifier (a provenance-licensed RC op without its category gate) | (a) backend unit (D1/D2 matrix — a compensation-shaped fix leaves classification wrong and those cells RED) + structural (`protect_return_value` untouched, no emission site gains a branch — design G2, `review` §8 reject criteria); (b) **reduced-corpus** golden byte-identity, entries 01–09 (`tests/clif_golden_lane.rs::clif_golden_lane_no_drift`) — compiler-focused fixtures, no exemplar authority; **measured constructor-half face:** the new reduced corpus entry, §3.2 | the 9 reduced entries of the 13-entry golden corpus; the D1/D2 module matrix | the corpus entry is captured post-fix (green-only rule), so its fix-time reading is `qa`'s one Wave-4 shape check (§3.2); byte-identity observes emission, not runtime balance (D6) |
| D6 | Composed outcome: the two 0917 marginal cells read exact 0 | a partial fix — residual between 1 and 4,402 on the pair | the existing focused e2e (this is why no duplicate cell is authored) | `tests/nullary_arm_beside_boxed_arm_0917.rs` | balance cannot name the mechanism (D5 does); REPL face not separately measured — accepted, the emission path is shared with `--run` and the pair spans both artifact modes; exemplar cell #21 is downstream observation (§3.1), not part of this condition |

**Residuals carried, not newly controlled** (no control is added without a
residual failure it uniquely detects): the `Trace`/`ParBind`/`LaunchContinue`
`OwnedTemporary` cap on a `NoReference` inner value (design §6.2.2, with its
two named revisit triggers), and the seam-by-seam-asserted category gate whose
falsifier D5(b)'s reduced-corpus sweep observes on its emission-visible face.

## 3. Downstream observation and generated-baseline maintenance

Everything in this section **observes consequences of the already-authorized
correction**. Nothing here gates, shapes, or blocks it; a surprising reading
here is defect intake (attribution to `qa`), never a stop condition keyed to
the exemplar.

### 3.1 The observers

1. **Exemplar cell #21**
   (`exemplar_ownership_residue_s116::sudoku_warm_serial_solve_residue_at_most_1400`)
   is the exemplar-shaped downstream observer of the same leak class. It
   remains unchanged and passes at its existing ≤1400 threshold. Its exact
   re-derivation, allocated by `tests/plan/s119-test-plan.md` §5.3, is
   downstream evidence maintenance rather than a condition of this compiler
   correction. A future nonzero exact residue is new intake routed to `qa`;
   it cannot reopen the compiler correction, whose acceptance stands on §2.
2. **The L-B1 golden lane.** Two distinct roles inside one 14-entry corpus:
   - **Entries 01–09** (`tests/fixtures/clif_baseline/corpus/`) are `qa`'s
     reduced compiler-focused fixtures — their byte-identity is *acceptance*
     evidence for the scalar half (D5(b)) and is expected unchanged.
   - **Entries f1–f4** are large-program fixtures; `f4_sudoku` is
     exemplar-derived and is **observation only**. The recorded static
     census (verified pre-change, `sprints/SPRINT.md` §Evidence log): the
     fix necessarily removes exactly one guarded protect-inc, the
     `f4_sudoku.clif` `user::eliminate` return seam (`block2`'s
     `icmp ult v10, v101`/`brif`/`atomic_rmw` add). That is a **prediction
     for reconciliation**, derived from design §6.2's verdict table plus the
     corpus census — not an acceptance shape the fix must be steered to.
   - **Maintenance is the lane's own standing discipline**, not a compiler
     acceptance decision. The generated `f4_sudoku` frame remains untouched
     in this correction, so the lane continues to report that downstream
     drift. Reconciling it later records an independently accepted change; it
     cannot become evidence *for* that change.
   - **Reconciliation:** drift beyond the predicted frame is defect intake —
     in entries 01–09 it fails D5(b) (compiler acceptance evidence, the
     §6.2.2 falsifier firing); in f1–f4 it is an observation finding routed
     to `qa` attribution. Either way `qa` weighs the open intake in its
     Wave-4 adequacy judgment; the golden itself decides nothing.

### 3.2 The one added compiler-focused condition (closing the D5 gap)

With `f4_sudoku` out of the acceptance chain, no reduced golden frame
exercises the corrected class. The smallest independent compiler-focused
condition: **extend the L-B1 corpus by one entry**,
`10_nullary_arm_beside_boxed_arm.cl` — the committed repro's own program
(subject mixed nullary/boxed match beside its all-boxed control, from
`tests/nullary_arm_beside_boxed_arm_0917.rs`). Extension ≠ re-baseline per
the manifest; the entry lands **with the fix** (the manifest's green-only
rule excludes shapes under open failing guards until then). At the final gate
`qa` reads the captured frame once against the design-derived shape: the subject's
return seam carries **no** former guarded protect-inc and agrees with the
control on that absence. This is the measured face of D5(a)'s elision claim;
thereafter the entry is an ordinary permanent emission pin for the class,
and the exemplar-derived frame is non-load-bearing for it forever.

**Final state.** The corpus input, golden, MANIFEST row and `ENTRIES` line are
present; the temporary EXCLUSIONS hold is gone. Two isolated,
manifest-equivalent captures were byte-identical (11 frames, 731 lines,
SHA-256 recorded in the final measured basis), and only the new entry was
retained. The subject return seam no longer carries the former guarded
protect-inc. Existing entries 01–10 and f1–f3 match; the untouched downstream
`f4_sudoku` drift is outside this condition.

## 4. Handoff — `test`

**No duplicate independent condition.** The discriminating RED exists and was
re-confirmed pre-change (0/2, marginal 4,402). `test`'s acts:

1. **Locus repair — DISCHARGED (W1, `qa`-verified):** in
   `tests/nullary_arm_beside_boxed_arm_0917.rs` (both cells) and
   `tests/exemplar_ownership_residue_s116.rs` (cell #21), the `// defect:`
   locus token is corrected to
   `crates/cranelisp-backend/src/compiler/rc_emission.rs::protect_return_value`,
   with one prose clause noting the token mis-cited `fn_compiler.rs` at
   filing (FIXME 0917 header is the record). `class=`, `found=`, `owner=`
   unchanged; the RED re-confirmed unchanged after the edits (see Measured
   basis).
2. **Corpus extension — DISCHARGED:** entry 10's input and golden are present,
   its MANIFEST and `ENTRIES` rows move together, and no EXCLUSIONS hold
   remains. The two-capture result and hash are recorded in §3.2.
3. **Commit-dependent metadata — pending, non-blocking:** the three repros
   cannot truthfully carry `fixed=S120/<sha>` until a closing commit exists.
   Cell #21's exact re-derivation and the untouched `f4_sudoku` reconciliation
   are downstream maintenance under §3, not compiler-correction gates.

Completion: three loci are corrected; entry 10 is wired and captured; only
commit-dependent `fixed=` metadata and downstream observer maintenance remain.

## 5. Handoff — `dev` (`cranelisp-backend`)

Implement `non-concrete-release-contract.md` §6.2 + §6.2.1 + §6.2.2 exactly
(no new emission licence arm; `protect_return_value` untouched; the
exhaustive `value_provenance` match keeps no `_ =>`). Module evidence is
enumerated (the enumerated-deferral discipline — each cell must fail on
revert of its slice of the fix):

- `NoReference` for: bare nullary-ctor `Var`; `Apply` whose callee is a
  zero-field ctor; fieldless `ConstrADT`; every scalar literal. `Fresh`
  unchanged for every minting kind.
- Ctor **with** fields referenced as a value stays `NotOwnedHere` under both
  probes (the UAF-direction fence, D1).
- Joins: `join(NoReference, Fresh) == Fresh`; `join(NoReference,
  NotOwnedHere) == NotOwnedHere`; N nullary arms + one boxed arm ⇒ `Fresh`;
  all-nullary ⇒ `NoReference` (seed at the identity); arm-less ⇒
  `NotOwnedHere` (the guard is load-bearing, D2).
- Both thresholds as ruled (D2); the three-state probe from the ONE
  `ctor_meta_at` read, agreeing with `nullary_constructor_tag`, no second
  probe or second field-list read (D3).
- The monotonicity pin with its detection proof, both legs (D4).
- Golden verification per §6.4 (D5): report the drifted-frame set against
  §3's prediction without steering the fix to satisfy exemplar output. Entry
  10 supplies the permanent compiler-focused pin; `f4_sudoku` stays an
  untouched downstream observation.

Release gate: `sprints/METHOD.md` §2.3 all four commands for
`cranelisp-backend`, zero new warnings. Existing fences that must stay GREEN:
the 0781 provenance cells, `tests/false_fresh_provenance_residual.rs`,
`tests/vec_assoc_param_mutate_return_uaf.rs`, the 0810/0726 match-ownership
guards, and `tests/marginal_harness_capability.rs`.

## 6. Completion criteria

Ordered as the authority runs: compiler acceptance first, downstream
observation last.

1. **Focused (compiler acceptance).**
   `cargo nextest run --test nullary_arm_beside_boxed_arm_0917`: 2 passed,
   both pairs exact marginal 0 (sprint acceptance item 1).
2. **Crate gate (compiler acceptance).** METHOD §2.3 checks, tests and module
   evidence are green with the D4 detection proof. Clippy reports the same 11
   lints before and after, all in untouched files: no new warning, but not a
   literal zero-warning surface. This deviation is explicit residual debt,
   not evidence that the 0917 change introduced degradation.
3. **Full suite.** `cargo nextest run --no-fail-fast`: the failed set is the
   recorded 20 minus exactly the three 0917-attributed cells, plus the golden
   lane's untouched downstream `f4_sudoku` drift: 17 traced compiler carries
   and one generated-observer failure; 1 skipped unchanged. Any other RED
   delta is a genuine regression and a stop.
4. **Compiler-focused generated evidence.** Entry 10 is present and
   deterministic; entries 01–10 and f1–f3 match. The untouched `f4_sudoku`
   drift keeps the aggregate lane RED and cell #21 retains its threshold form;
   both are downstream maintenance under §3 and neither authorizes or blocks
   the correction.

## 7. Blockers and owner decisions

- **Former B-1 — dissolved (authority-direction error, this revision's
  correction).** The prior revision treated the exemplar-derived golden's
  pinned bytes as a gate on the compiler correction and escalated for a user
  ruling to change it. The user ruled the direction: the exemplar and its
  derived golden observe only. It remains untouched and is downstream
  maintenance, not an acceptance blocker.
- **Former B-2 — dissolved.** The sprint record explicitly allocates the
  test-owned entry-10 extension while retaining the prohibition on changing
  existing golden output. Only the new compiler-focused artifact was retained;
  no scope ambiguity remains.

## 8. Final adequacy verdict

**Blocking findings: none. Required findings: none. QA recommends user
acceptance of the bounded 0917 compiler correction.** The authority chain is
requirement → approved backend design → direct run/link outcome → backend
module invariants → reduced compiler-focused emission pin → independent
review. Each layer discriminates a distinct plausible wrong outcome, and the
exemplar is absent from that chain.

The independent review found no backend correctness defect. Its advisory
maintenance-weight finding is valid: the private two-variant classification
has more narrative than its mechanism needs, the two determinant tests overlap
logically, and the standing backend `CLAUDE.md` repeats design history. The
private type and shared determinant still earn their existence by preventing
lowering/provenance disagreement; the excess prose and duplicate negative
branch evidence do not weaken correctness or leave a condition unobserved.
They are non-blocking maintenance debt owned by `dev`, with `qa` responsible
for not requiring duplicate evidence. No correctness-sensitive correction was
made after review, so a re-review is not warranted.

Non-blocking residuals:

- Clippy reports 11 lints before and after, all in untouched files. The change
  adds none, but the crate does not literally meet METHOD §2.3's zero-warning
  wording.
- The full suite retains 17 traced compiler-defect guards outside 0917. No new
  compiler failure appears.
- The untouched downstream `f4_sudoku` drift keeps the aggregate golden lane
  RED, and exemplar cell #21 still uses its passing threshold rather than the
  separately allocated exact re-derivation. Neither result can shape, block or
  reopen this correction.
- The three repros cannot receive truthful `fixed=S120/<sha>` metadata until a
  closing commit exists. That metadata is commit-dependent close work, not
  missing behavioral evidence.

This verdict recommends acceptance; `sprint` and the user retain authority to
accept and close the increment.
