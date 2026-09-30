---
id: ACT-1030
title: A self-tail argument that forwards a released binding through a `let` gets no owned reference, so the parameter flush frees a box the next iteration reads
status: open
priority: required
from: qa
to: qa
sprint: 122
filed_at: 2026-09-30
refers_to:
  - crates/cranelisp-backend/src/compiler/apply.rs::compile_tail_self_call
  - crates/cranelisp-backend/src/compiler/rc_emission.rs::protect_return_value
  - crates/cranelisp-backend/src/compiler/control_flow/let_if.rs::compile_let_sequential
  - crates/cranelisp-backend/src/compiler/fn_compiler.rs::protect_escaping_borrows_before_tail_jump
  - design/backend/ownership-codegen.md §13.3
  - tests/vec_push_match_binder_same_name_shadow.rs
  - tests/plan/s122-evidence-delta.md
  - spec/12-runtime.md §12.3.1
---

## Observation

This use-after-free was **observed**, in the renamed-binder control of the
ACT-1029 probe (`.local/s122-1029-probe-test-result.md`; raw log
`.local/s122-1029-probe-t0/nextest-run.log`). The program should exit 3:

```
(import [primitives [Pure add-i64 eq-i64 vec-len vec-push]])
(defn go [n p q]
  (if (eq-i64 n 0)
      (add-i64 (vec-len p) (vec-len q))
      (match q [alias
        (go (add-i64 n -1)
            (vec-push q 1)
            (let [t (match p [b b])] alias))])))
(defn main [] (Pure (go 3 (vec-push [] 1) (vec-push [] 9))))
```

- Under `--run --no-cache` with `CRANELISP_RC_DEC_CHECK=1`, it stopped with
  `USE-AFTER-FREE` in `vec_push_copy(src)`, on a buffer `vec_drop` had freed.
- The run printed no counters.
- This program has no same-name binder, so ACT-1029's mechanism does not
  apply.

## Attribution

- **Status: provisional.** The mechanism is a source-read hypothesis, and no
  discriminating control has run.
- **Hypothesis:** the `let`-wrapped tail argument yields `q`'s box, through
  the borrowed view `alias`, with no owned reference. The parameter flush
  then releases `q`'s slot.
  - `tail_arg_protect` is armed only for a top-level `if` or `match`.
  - The escape-borrow upgrade and the transfer slots read only a bare
    top-level `Var`.
  - `t` is marked borrowed, so the `let` frame has no cleanup target, and
    `protect_return_value` adds no increment.
  - This is the face of leads L6 and L2 (`ownership-codegen.md` §13.3) at a
    top-level `let` argument.
- **Consistent evidence.**
  - `q` is the only push source.
  - A-T's subject makes the same tail call with a bare `alias` and was GREEN
    at K4 step 1.
- **Entry: predicted pre-existing.** The three gates are unchanged from
  `e4062202`. This is not measured at HEAD.
- **Refuted if** the single-change control balances no better: the same
  program with an owned binder added,
  `(let [t (match p [b b]) u (vec-push [] 0)] alias)`, still stops armed.
- **Predicted without a match binder:** `(go … (let [t 0] q))` should fault
  the same way. This is unmeasured. It matters to the design question, not to
  this attribution.

## Evidence

The settled delta is the L6 cell in
[the evidence delta](../../tests/plan/s122-evidence-delta.md#act-1029-r1-probe--t0-control-fault-and-redesigned-delta-2026-09-30).
It includes each half observed on its own and a CLIF seam observation.
`tests/vec_push_match_binder_same_name_shadow.rs` stays the failing guard for
this fault until the L6 cell is RED for its intended reason.

## Disposition

- **If confirmed:** `design`(backend) decides one rule for any non-bare
  tail argument that forwards a binding the jump releases; then
  `dev`(backend) implements it.
- **Fix or carry** is the user's decision.
- **Until then**, QA retains this intake.

## Completion evidence

One of these:
- the L6 control also stops, so QA re-attributes this intake;
- the L6 cell goes RED for its intended reason, then GREEN after the
  correction, with its control balanced.
