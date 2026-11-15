---
id: ACT-1026
title: A let or match that yields its own binder, consumed in the same frame, never releases the value
status: resolved
priority: required
from: qa
to: qa
sprint: 122
filed_at: 2026-09-30
refers_to:
  - tests/join_forwards_its_binder.rs::match_yielding_its_binder_consumed_in_frame_releases_the_value
  - tests/join_forwards_its_binder.rs::let_yielding_its_binder_consumed_in_frame_releases_the_value
  - crates/cranelisp-backend/src/compiler/fn_compiler.rs
  - crates/cranelisp-backend/src/compiler/match_codegen.rs
  - crates/cranelisp-backend/src/compiler/rc_emission.rs
  - tests/cow_result_consumed_in_frame.rs::parameter_set_at_its_last_use_and_forwarded_by_a_match_arm_balances
  - tests/plan/s122-evidence-delta.md
  - spec/12-runtime.md §12.3.1
---

## Observation

`test`'s V1 visit found W-M's committed control leaking one block
(`.local/s122-backend-v1-test-result.md` §3). QA reduced it
(`.local/s122-1024-v1-qa/`, armed, `--no-cache`, on the working-tree binary
`a423324d…` and the HEAD `e4062202` export `733c7335…`).

- **Leaking shapes** (residual 1, both revisions, analysis on and off):
  - `(defn f [] (vec-len (match [1 2] [r r])))`;
  - `(defn f [] (vec-len (let [r [1 2]] r)))`;
  - the same with `(vec-push [] 1)` as the value.
- **Balanced controls:**
  - the join returned from `f` and consumed by the caller;
  - the join bound by `let`;
  - an arm that consumes `r`.
- **Seam (CLIF of `main::f`).** The join hands its binder's reference out
  (`skip_var`, or the `OwnedForwarded` plan). `vec-len`'s temporary release
  does not fire, because `value_provenance` classifies a join whose value is a
  `Var` as `NotOwnedHere`. Neither side releases the value.
- **Class:** `rc-miscount`, a leak. It is not memory-unsafe.
- **Coupling.** W-M's subject balances only because this missing release
  cancels ACT-1024's missing increment. The copy-branch counterpart,
  ACT-1027 (corrected in the uncommitted S122 tree, filing deleted
  2026-09-30), is the same ownership question for a retaining COW scrutinee.

## Attribution

**Mechanism observed at CLIF.** The disagreement is between the join's
transfer and the consumer's provenance answer. The R3 ruling places the fix on
the provenance side (Disposition, below;
[V1 record](../../tests/plan/s122-evidence-delta.md#act-1024--v1-record-and-the-w-m-ruling-2026-09-30)).

- **Refuted if** either reduced shape balances armed while its control is
  unchanged.
- **Not claimed here.** The `let`-bound `vec-set` leak returned from `f`
  (`d2c_ctl`, its in-place twin, and the sibling `b2`) is
  [ACT-1028](ACT-1028-let-bound-vec-set-returned-leak-intake.md), with its
  attribution unknown.

## Disposition

**Carried to S123 (user, 2026-09-30). S122 implements none of it.** This is
the first deferral. The governing record is the
[approved R3 delta](../../tests/plan/s122-evidence-delta.md#act-1024-with-the-r3-retirement--approved-evidence-delta-2026-09-30).

- **Side settled.** The R3 ruling (`ownership-codegen.md` §13.7) keeps the
  join's transfer. The provenance walk that reads a forwarding join as
  `NotOwnedHere` is the side to change.
- **Carried REDs,** failing and not ignored: D1-M and D1-L (V1b, measured
  at marginal 1).
- **W-M pins this action's one block.** It asserts `assert_residual(1)` until
  this correction lands, and this correction restores `assert_balanced` in
  its own change-set.
- **Widened exposure, disclosed.** ACT-1024's retention removes the missing
  increment that cancelled this leak on the mutate branch. So one block now
  leaks per evaluation, or per loop iteration, for any forwarding join over a
  `Var`-sourced COW whose result reaches an in-frame consumer. On the copy
  branch these shapes leak already. The faces:
  - W-M's subject (measured balanced before the fix; predicted +1 after);
  - `(vec-len (let [r (vec-push v 0)] r))`, which needs no `match`
    (predicted);
  - a nested forwarding match whose value is returned: 0668 cell B, which
    asserts only its value (predicted);
  - W-M with a shared source (measured +1 before the fix, unchanged).
  - None is predicted to become a use-after-free.
- **Any V2 RED attributed here** stays RED and joins this list. It gets no
  residual pin.

**S123 needs, before `dev`:**

- a `design`(backend) pass on R3 ruling §8: one ownership answer after
  compilation, read by every temporary-release gate;
- a census of every `yields_owned_temporary` consumer, because the change
  moves gates toward releasing, which is the use-after-free direction;
- QA's allocation, including a measurement of the predicted faces above.

## Completion evidence

- D1-M and D1-L are GREEN, with their controls balanced.
- W-M is restored to `assert_balanced` and is GREEN.
- The S123 census shows no consumer releasing a value it does not own. The
  unit tier for each changed gate was observed RED first.

## W2 disposition (qa, 2026-11-16)

U′ corrects the leak, but one completion item is still missing.

- **Source opened.** `crates/cranelisp-backend/src/` on the W2 tree: `value_provenance`, `yields_owned_temporary`, `compute_last_uses`, `register_alias`, `tail_arg_protect`, `protect_escaping_borrows_before_tail_jump`, `protect_return_value` and `scrutinee_lifetime_for_arm` no longer exist ([uniform counting §5](../../design/backend/uniform-counting.md#5-what-retires)). With those deciders gone, the census of
  `yields_owned_temporary` consumers is moot: every position consumes.
- **Evidence.** D1-M and D1-L, and `uniform_counting::forwarding_{match,let}_balances_*`,
  were assertion-RED at residual 1 on the checkpoint compiler `ee8959c0…`
  (`.local/s123-w2/test-evidence.md`). They pass on the U′ tree, with their
  controls balanced.
- **Run.** QA's targeted run on 2026-11-16 (compiler `86402bc0…`, U′ tree): `uniform_counting`, `join_forwards_its_binder`, `vec_push_match_binder_same_name_shadow` and `tco_tail_arg_alias_uaf` all pass.
- **Blocks resolution.** W-M,
  `cow_result_consumed_in_frame::parameter_set_at_its_last_use_and_forwarded_by_a_match_arm_balances`,
  now **fails**. It measures residual 0 against its `assert_residual(1)` pin,
  with both halves at 2/2. `test` restores `assert_balanced`
  ([evidence delta](../../tests/plan/s123-evidence-delta.md#39-w2-intake-on-the-u-tree)
  U-13). QA resolves this action when W-M passes, and `fixed=` is stamped at
  the W2 commit.

## Resolution (qa, 2026-11-16, S123 W2)

The blocking item is met.

- **Source opened.** `tests/cow_result_consumed_in_frame.rs`:
  `parameter_set_at_its_last_use_and_forwarded_by_a_match_arm_balances` now
  ends in `assert_balanced` (U-13).
- **Run.** QA's full suite on the U′ subject `77bb2dd9…` passes W-M, D1-M,
  D1-L and `uniform_counting::forwarding_{match,let}_balances_{run,link,repl}`.
- **Owed.** At the W2 commit, `test` stamps `fixed=` on D1-M, D1-L and the six
  forwarding cells. Delete this action once its inbound links are repointed.
