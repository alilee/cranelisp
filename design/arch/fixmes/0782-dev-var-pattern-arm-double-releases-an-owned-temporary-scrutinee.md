---
number: 0782
target: /dev
filed_by: /dev
filed_at: 2026-07-21
sprint_filed: 115
refers_to: crates/cranelisp-backend/src/compiler/match_codegen.rs::compile_var_pattern_arm
  (the `is_alias` scope registration) + ::dec_temporary_scrutinee — both fire for
  a genuinely-owned temporary scrutinee under a var pattern, releasing it twice
status: open
---

# A var-pattern arm over an OWNED temporary scrutinee releases it twice (`--link` 134)

## Severity

**Blocker** (memory-safety double-free, `--link` exit 134). **Pre-existing**,
measured at `509cd9da` and unchanged by the W4c change-set — verified by
building the parent tree and running the repro there.

## Issue

Found while fixing 0781 in the same seam; it is a DIFFERENT defect and is
deliberately NOT fixed in the W4c change-set (no committed repro exists, and
choosing which of the two releases is correct is a seam decision better made
with `/testing` cover in place — METHOD §2.2 repro-before-fix).

### Repro (`PrimitivesOnly`, `--link`)

```
(defn f [] (match [7 8 9] [xs (vec-get xs 1)]))
(defn main [] (Pure (f)))
```

→ **exit 134, `corrupted double-linked list`** at `509cd9da` AND at the W4c
tree. Expected exit 8.

### Discriminating control (METHOD §2.2)

The identical program with the scrutinee spelled as a **binding** —
`(defn f [] (let [v [7 8 9]] (match v [xs (vec-get xs 1)])))` — is clean, and
so is the non-consuming forwarding form `(match [7 8 9] [r r])`. The variable
isolated is therefore exactly *"the scrutinee is an owned temporary AND the arm
consumes it"*, not the vec literal, not the match, not `vec-get`.

### Mechanism observed at the seam

Two independent release paths both fire for an owned temporary under a var
pattern:

1. `compile_var_pattern_arm` — `is_alias` is false for a non-binding scrutinee,
   so the pattern name is pushed onto `scope_stack` and `pop_scope_with_cleanup`
   decs it at arm exit;
2. `compile_match`'s merge block — `match_forwards_scrutinee(arms)` is false
   (the arm body is `(vec-get xs 1)`, not `xs`), so `dec_temporary_scrutinee`
   decs the same pointer again.

CLIF for the reduced body carries **two** `atomic_rmw.i64 sub` on the same
value where one is owed. The two gates are exact complements on the OWNERSHIP
question (that complementarity is what W4c preserved), but complementarity does
not stop both firing — the alias registration and the consume are different
questions, and nothing reconciles them.

### Falsifiability

If the arm-exit cleanup dec and the merge-block consume dec were on different
pointers (e.g. the alias slot held a protected copy), the double-release
attribution is wrong and the abort is elsewhere. Refute by dumping the CLIF for
the reduced body and checking whether both `atomic_rmw.i64 sub` operands trace
to the same scrutinee value; they did when measured, but the receiving `/dev`
should re-run that check first.

## Proposed resolution

Pick ONE owner for a consumed owned-temporary scrutinee and delete the other
path — the candidates are (a) never register the alias for scope cleanup (the
merge-block consume is the single release), or (b) register it and suppress the
merge-block consume when a var-pattern arm bound it. (a) looks right: the
scrutinee's release is already the merge block's job for constructor arms, and
the alias is a borrow of a value the match frame owns for the arm's duration.
Whichever is chosen, the two gates should read the ONE derived answer as they
now do for ownership, not acquire a third condition each.

Needs `/testing` for the e2e cell (requested in-wave, not deferred — METHOD
§2.2 / FIXME 0765): the repro above plus the two controls, `--run`/`--link`/REPL.

## /qa S118 W1+ re-measurement (2026-07-25) — mechanism LIVE at HEAD; the e2e green is layout-latent, NOT a fix

The committed guard
(`match_owned_temporary_scrutinee_0810::var_pattern_arm_consuming_owned_temporary_releases_it_once_linked`)
went GREEN at HEAD `e15ff20f` with no fix landed. Per the S98 rule `/qa`
re-ran this FIXME's own falsifiability check at HEAD (`/clif f` over the
exact repro, empty prelude): **both `atomic_rmw.i64 sub` are still emitted
on the SAME scrutinee** (`v24 = iadd_imm v4, 8` in the arm-exit block,
`v33 = iadd_imm v4, 8` in the merge block, each followed by a conditional
free of `v4`). The double release is deterministic in the IR; only the
`--link` allocator abort is layout-latent. The receiving `/dev` should
treat the repro's current exit-0 as meaningless: acceptance is ONE release
in this CLIF shape + the guard staying green, with the unit pin counting
releases at the seam. Record: `tests/plan/s118-test-plan.md` §2.6.

## Context

- FIXME 0781 (this seam, W4c) — the ownership-gate half, fixed; its unit pin
  `match_codegen/scrutinee_ownership_tests.rs::fresh_vec_literal_scrutinee_still_releases`
  deliberately asserts "at least one release" rather than a count, so it does
  not freeze the wrong number this FIXME must change.
- `crates/cranelisp-backend/CLAUDE.md` §"RC-emission gates that are ONE
  predicate, not per-site syntax".
