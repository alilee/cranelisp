---
number: 0772
target: /dev
filed_by: /review
filed_at: 2026-07-21
sprint_filed: 115
refers_to: crates/cranelisp-typecheck/src/ownership/transfer.rs::join_origin
  (the same-param/same-kind arm, ~:370-378) — the §17.2 row-4 UNION is computed
  and then DISCARDED when the first operand is not a `Conditional`
status: open
---

# `join_origin` discards the §17.2 cow link-set in one arm order → order-dependent unprotected may-alias link (`--link` UAF)

## Severity

**Blocker** (memory-safety UAF; falsifies the shipped §17.3 family-grain
acceptance claim). NOT a regression — probe-confirmed RED at `d4efdf08~1` too —
so `/sprint` may legitimately dispose it as a scoped carry. It is filed at
Blocker because the wave's acceptance argument asserts the opposite.

## Issue

`join_origin` computes `let cow = union_cow(a.cow_spans(), b.cow_spans());` and
then, in the same-param/same-kind arm, keeps it only when `a` happens to be a
`Conditional`:

```rust
match a {
    Origin::Conditional { rep, projection, .. } => Origin::conditional(rep, projection, cow),
    other => other,     // <-- `cow` is DROPPED here
}
```

When `a` is `Unconditional` and `b` is a `Conditional` carrying may-alias links,
the whole link-set is silently discarded, the join result has no `cow` field at
all, and the row-6 projection-out force at `transfer.rs:~790` never fires for
those links. The answer therefore depends on **incidental arm order** — the P24
acid test ("does the answer depend on incidental order?") fails.

`MonoExpr::If` walks `then` then `else` and calls `join_origin(a, b)` in that
order (`transfer.rs:479-483`), so the hole is directly reachable from source
order.

### Probes (this VM, HEAD `d4efdf08`, `PrimitivesOnly`, `--link`)

| Probe | Source | `--run` | `--link` |
|---|---|---|---|
| cow arm SECOND | `(defn f [v b] (vec-get (if b v (vec-set v 0 1)) 0))` + `(f [9 9 9] false)` | 1 (correct) | **134 `corrupted double-linked list`** |
| cow arm FIRST (twin) | `(defn f [v b] (vec-get (if b (vec-set v 0 1) v) 0))` + `(f [9 9 9] true)` | 1 | 1 ✅ |

The two programs execute the *same* runtime path (both take the `vec-set`
branch); only the static arm order differs. A dynamic condition (`b` a
parameter) rules out constant folding.

A second, broader shape aborts in **both** arm orders — so the let-mediated
binding feeding an `If`-joined container is not covered at all:

| Probe | `--link` |
|---|---|
| `(defn f [v b] (let [w (vec-set v 0 1)] (vec-get (if b v w) 0)))` | **134 `free(): chunks in smallbin corrupted`** |
| `(defn f [v b] (let [w (vec-set v 0 1)] (vec-get (if b w v) 0)))` | **134 `free(): chunks in smallbin corrupted`** |

### What the change-set DID fix (verified against `d4efdf08~1`)

The family fix is real and generalizes beyond the two pinned faces — a
three-link nested chain
`(vec-get (vec-set (vec-set (vec-set v 0 1) 1 2) 2 3) 0)` was **134 at the
parent commit and is exit 1 (clean) now**. Cross-function chains, nested `let`
chains, and mixed nested/`let` chains all probe clean. The negative direction is
also clean: `CRANELISP_RC_STATS` shows `allocs == deallocs` on the chained and
whole-value-control shapes (no spurious retain / leak from the widened force),
and the whole-value nested-transfer control is byte-for-byte unchanged against
the parent binary.

## Proposed resolution

In the same-param/same-kind arm, do not let the `Origin` *variant* of the first
operand decide whether the link-set survives. When `cow` is non-empty the joined
value carries may-alias links regardless of which operand contributed them —
widen to `Origin::conditional(rep, projection, cow)` (monotone; the set only
grows, and `Conditional` is already the safe over-claim direction this arm's own
comment invokes). Then re-probe the `let`-mediated `If` shape above, which is
failing in both orders and may need row 2/row 4 composition through the binding
env as well.

**Repro cells are owed before the fix** (METHOD §2.2 repro-before-fix): see
FIXME 0773 (`target: /testing`) for the e2e lane cells, plus a `/dev` unit cell
at the `join_origin` seam asserting the link-set survives in BOTH operand
orders — the unit tier currently has no order-symmetry cell, which is exactly
why this passed review-by-suite.

## Context

- Design of record: `design/typecheck/ownership-inference.md` §17.2 row 4
  ("`join_origin` UNIONs the arms' cow-alloc span-sets **when the join is
  Conditional**") and §17.3 ("the single pre-existing projection-out arm
  discharges every link of every chain shape"). The row-4 wording is literally
  satisfied by the as-built code, but §17.3's family-grain claim is falsified by
  the probes above — see FIXME 0777 (`target: /design`).
- §17.4 marked the `If`/`Match` container (face 3) "probe-first, no
  pre-committed arm" and predicted row 4's union "WOULD cover it". The probe has
  now been run and the prediction is **falsified in one arm order**.
- §17.6's carrier-enrichment tripwire is NOT implicated: the fix is entirely
  walk-internal; no `cranelisp-types` edit, no `CACHE_SCHEMA_VERSION` bump.
