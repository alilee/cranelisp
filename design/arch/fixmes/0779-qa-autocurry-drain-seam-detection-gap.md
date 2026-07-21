---
number: 0779
target: /qa
filed_by: /dev
filed_at: 2026-07-21
sprint_filed: 115
refers_to: crates/cranelisp-typecheck/src/program/mono_collect.rs::resolve_auto_curry
  — five of the six drain seams have NO unit-tier detection; a discipline flip at
  any of them leaves the whole `cranelisp-typecheck` tier green
status: open
---

# The auto-curry drain's seam/discipline mapping has detection at ONE of six seams

## Severity

**Important** — a coverage-process gap, measured not asserted. It is the
instrument half of FIXME 0775 (whose structural half — the required parameter —
landed S115 W4b).

## Issue

0775 asked for two things: make `AutoCurryDrain` a required parameter at every
call site (done — the defaulting wrapper is deleted, so a new seam cannot inherit
`Final` silently), and **unit-pin the seam/discipline mapping**. The second half
is only ⅙ satisfied, and I measured exactly how far.

Method: flip each of the six seams to the OPPOSITE discipline, one at a time, and
run the full `cranelisp-typecheck` unit tier (807 tests).

| Seam | Discipline | Flip | Unit-tier REDs |
|---|---|---|---|
| `program/body.rs:88` (single-sig body post-pass) | `Deferrable` | →`Final` | **1** — `mono_collect::tests::autocurry_over_trait_operator_never_carries_the_decl_fq` |
| `program/body.rs:441` (per-multi-sig-clause post-pass) | `Deferrable` | →`Final` | **0** |
| `program/finalize.rs:607` | `Final` | →`Deferrable` | **0** |
| `traits/monomorphise.rs:856` | `Final` | →`Deferrable` | **0** |
| `traits/impl_check.rs:762` | `Final` | →`Deferrable` | **0** |
| `traits/impl_check.rs:1024` | `Final` | →`Deferrable` | **0** |

The e2e tier partly covers the finalize seam (`tests/fn_as_value_carrier_loss.rs`
is the `'='` face whose resolution the settled finalize drain supplies); the other
four were not swept e2e.

Why the per-variant seam resists a naive twin cell: I authored
`mono_collect::tests::autocurry_in_a_multi_sig_clause_never_carries_the_decl_fq`
as the definition-variant twin, and it is GREEN and stays green under the
`:441` flip — the 1-arity clause stays a `$Var` template, so the observable
carrier is minted by the mono-body RECHECK (itself a `Final` seam), which
re-derives it from settled state whatever the per-variant drain concluded. The
cell says so in its own comment rather than posing as a pin it is not
(FIXME 0767/0768 — "matrix-verified requires a detection proof").

## Proposed resolution

`/qa` decides the shape; two candidates from the `/dev` side:

1. **A seam-level cell per discipline**, driving `resolve_auto_curry` directly
   over a seeded `pending_auto_curry` (the `join_lattice_*` cells landed in
   `ownership/transfer/tests.rs` this wave are the template — seam-level property
   cells over the operand set, no program shape to fight). This tests the
   FUNCTION's two polarities exhaustively; it does not test that each SEAM passes
   the right one.
2. **A per-seam behavioural cell**, needing a program shape whose settled
   carrier differs by discipline at that seam — which is the hard part for the
   four recheck-scoped seams, since a recheck is settled by construction.

If (2) is judged not worth its cost for the recheck seams, the honest disposition
is to record that in `tests/plan/` — "these four seams are `Final` by
construction, not by test" — rather than leave a silent gap.

## Context

- FIXME 0775 (`target: /dev`, resolved S115 W4b) — the P18 structural half.
- FIXME 0776 (`target: /arch`) — the settlement-seam-multiplicity class this is
  the fourth instance of.
- `design/backend/s115-carrier-and-rc-sweep.md` §1.3 — the boundary rule the
  discipline enforces.
