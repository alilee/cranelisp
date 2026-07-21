---
number: 0747
target: /design
filed_by: /dev (cranelisp-backend, S115 W3)
filed_at: 2026-07-21
sprint_filed: 115
refers_to: design/backend/s115-carrier-and-rc-sweep.md §6; design/backend/binding-indirection-consume.md §5 W-B5 row; crates/cranelisp-backend/src/compiler/fn_compiler.rs::{return_var_in_scope, operand_live_binding_root}
status: open
---

# W-B5's two acceptance clauses are mutually exclusive: collapsing `skip_var` onto the provenance classifier CANNOT be byte-identical-off

## Severity
Important (the change-set cannot be executed as specified; its acceptance gate
rejects the only faithful implementation of its own mechanism).

## Issue

W-B5 asks for two things at once:

1. **mechanism** — "collapse the three fn-return patches
   (`skip_var` / `protect_return_value` / `return_cow_source`) onto the ONE
   provenance contract" (`s115-carrier-and-rc-sweep.md` §6;
   `binding-indirection-consume.md` §5 W-B5 row);
2. **acceptance** — "NO flips — this is a byte-identical-off refactor; goldens
   byte-identical-off and CERTIFIED".

The two patches disagree by construction, so (1) necessarily violates (2):

- `return_var_in_scope` (`fn_compiler.rs`) — the `skip_var` producer — matches
  **only** `MonoExpr::Var`, and only when the name is in the CURRENT scope frame.
- `operand_live_binding_root` — the ONE provenance contract (the W-B1
  classifier) — deliberately traces **through binding-indirection**: `Let`-body
  forward, and `Match` scrutinee forward when `match_forwards_scrutinee`.

So for any function whose returned value reaches a live binding THROUGH a `let`
or a forwarding `match`, the classifier says `Some(root)` where
`return_var_in_scope` says `None`, and collapsing the two changes emission.

### Worked witness (measured, `--run --no-cache`, `CRANELISP_NO_OWNERSHIP=1`)

```clojure
(defn f [v] (let [x 1] v))
```

emits today (`wb5/f$String`):

```
    v5 = atomic_rmw.i64 add v3, v4     ; protect_return_value inc on the returned param
    v8 = atomic_rmw.i64 sub v6, v7     ; pop_scope_with_cleanup dec of the same param
    brif v9, block3, block2            ; …and its rc==0 teardown branch
```

Under the collapse the classifier yields `skip_var = Some("v")`, so BOTH RC ops
and the teardown branch disappear. The result is equally correct (the pair is a
net no-op) and strictly better code — but it is **not byte-identical**, and if
this shape appears in any golden frame the lane drifts.

## Proposed resolution

`/design`(backend) picks one and re-states §6 accordingly:

- **(a) keep byte-identity, narrow the mechanism** — collapse only where the
  classifier and `return_var_in_scope` provably agree (the bare-`Var` return),
  i.e. re-express `skip_var` as `operand_live_binding_root` RESTRICTED to the
  `Var` arm. That is a rename, not a collapse, and leaves the "three ad-hoc
  patches for one flow" complaint 0668 raised substantially open — worth saying
  so explicitly if it is the choice.
- **(b) keep the mechanism, replace the acceptance** — accept a SCOPED,
  certified golden re-baseline for the frames that lose the redundant
  inc/dec pair, with the acceptance restated as "RC-neutral per frame" (every
  drift hunk removes a matched inc+dec pair and nothing else) rather than
  "byte-identical". This is the honest bar for a refactor whose whole point is
  to make one predicate serve three sites.

Note that S115 W3 change-set 2 already moved `protect_return_value`'s LICENSE
onto a shared structural predicate (`is_fresh_construction`, now a pure free
function used by both the fn-return and match-arm protect sites), so the
`protect_return_value` third of the collapse is partly discharged; what remains
is the `skip_var` / `return_cow_source` pair.

## Context

W-B5 was NOT executed in S115 W3. Deferring it for size would be the wrong call
(the standing no-defer-for-size rule); it is deferred because its acceptance
gate, as written, rejects its own mechanism — a design question `/dev` must not
settle unilaterally. FIXME 0696 (the name-keyed F-R1 predicate, which was
scheduled to ride W-B5) is INDEPENDENTLY RESOLVED and deleted: change-set 2
implemented its design ruling direction (b) directly.
