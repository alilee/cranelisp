---
number: 0774
target: /dev
filed_by: /review
filed_at: 2026-07-21
sprint_filed: 115
refers_to: crates/cranelisp-typecheck/src/program/register/multi_sig.rs:686-707
  — the FIXME-0719 self-call arm carries a 21-line comment describing a callee
  retype that is not implemented; `record_expr_type` appears only at :761
  (concrete arm) and :805 (template arm)
status: open
---

# The 0719 self-call arm is a COMMENT ONLY — it documents a retype that does not exist

## Severity

**Important** (correctness of the record, not of behaviour today; a future
reader will believe this arm is covered).

## Issue

The S115 W4 change-set applied the FIXME-0719 "retype the callee node from
settled state" to three arms of `resolve_one_overload_call`. Two of them contain
code; the self-call arm contains only the comment:

```rust
state.deferred_self_call_dispatch.push((span, base_name.clone(), variant_index));
// FIXME 0719 (§11.8.11) — RETYPE THE CALLEE NODE from settled state.
// Mirror of the inline dispatch arm in `infer.rs::infer_apply` …
// The dispatch DECISION is settled here … so the node's type is
// recorded from that decision, not re-derived later. …
return Ok(());          // <-- no record_expr_type
```

`grep -n 'record_expr_type' register/multi_sig.rs` → `:761`, `:805` only. The
self-call arm records nothing, and `callee_span` is not carried in the
`deferred_self_call_dispatch` tuple `(span, base_name, variant_index)`, so no
later drain can supply it either.

The W4 disclosure to `/sprint` states that the self-call and template arms were
"kept to avoid a per-arm mirror" and are unproven. That is accurate for the
template arm; for the self-call arm there is nothing to prove — the change was
not made. A comment that asserts behaviour the code does not have is worse than
an absent comment (Principle 7 — the code and its record must have one source of
truth).

## Proposed resolution

Pick one, deliberately:

- **(a) Implement it.** Thread `callee_span` through and call
  `record_expr_type(state, callee_span, Type::Fn(param_types_after_unify, ret))`
  before the `return Ok(())`. The unify immediately above IS the settlement this
  arm's own comment invokes, so the datum is available. Pin it with a unit cell
  (a self-recursive multi-sig consumed through a wrapper) — otherwise it is a
  third unpinned arm.
- **(b) Do not implement it.** Replace the comment with an explicit statement of
  why the self-call arm does **not** need the retype (candidate reason: the
  deferred `SigDispatch` is derived post-drain in
  `finalize_multi_sig_variant_types`, and the §11.3.2 B1 deferral means the
  callee node's type is grounded by the final `resolve_expr_types` subst
  application) — and say so as a *reason*, not as a description of an action.

(b) is the cheaper honest answer if no shape exercises it; (a) is right if
uniform application (P7) is the intent the wave claimed.

## Context

- `design/typecheck/monomorphisation.md` §11.8.11 — the 0719 design; it names
  the window-3 re-derivation, not a per-arm mirror.
- Bisect evidence (per the W4 disclosure) shows only the **concrete** arm
  (:753-765) is load-bearing; it alone is pinned by
  `register::multi_sig::tests::wrapper_indirected_multi_sig_return_monomorphises_from_settled_state`.
- The template arm (:801-809) is real code with no pinning cell — see the
  `/review` report's Suggestion; it should either gain a cell or be reverted.
