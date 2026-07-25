---
number: 0877
target: /qa
filed_by: /design (cranelisp-backend, S118 Phase 3)
filed_at: 2026-07-25
sprint_filed: 118
refers_to: design/arch/fixmes/0835-slist-sexp-construction-corrupts-the-heap-at-small-sizes.md;
  crates/cranelisp-primitives/src/marshal.rs:160-217 (deep_rc_inc_slist, sconcat);
  crates/cranelisp-intrinsics/src/drop.rs:134-155 (consume_slist);
  design/backend/transitive-drop-glue.md §7.2; tests/plan/s118-test-plan.md §4
status: open
---

# 0835 has no committed repro, and its leading mechanism candidate is not in the backend

## Issue

S116 arch ruling 1 orders the Track-B consumer migration "0835 first", and
ruling 1(a) requires "controlled reduction and permanent repro for the
corruption face" **before** migration. Neither exists at HEAD:

- no `tests/*0835*` file and no `// defect:` cell citing 0835 anywhere in
  `tests/`;
- no `PLAN.md` row;
- 0835 is absent from the S118 28-name baseline (`s118-test-plan.md` §2.1) and
  from the §4 Track-B acceptance matrix.

FIXME 0765 ("no fix without a repro precondition") therefore blocks the slice as
scheduled, and `/dev`(backend) has no acceptance cell that could turn green.

## The mechanism candidate — and why it is not backend's

Read at HEAD, `cranelisp_primitives::marshal::sconcat` (`marshal.rs:195-217`)
calls `deep_rc_inc_slist(ys)`, which adds **+1 to every `SCons` node and every
element** of `ys` (`marshal.rs:160-171`). It balances that with
`consume_slist(ys)` (`cranelisp-intrinsics/src/drop.rs:134-155`), which
**returns at the first node whose `old_rc != 1` and never descends**. After the
deep inc no node has `rc == 1`, so `consume_slist` decrements the head only.

Trace one tail node `D` of `ys` (caller holds `ys`, so head `H.rc == 1`,
`D.rc == 1`):

| step | `H.rc` | `D.rc` |
|---|---:|---:|
| call-site consuming inc | 2 | 1 |
| `deep_rc_inc_slist(ys)` | 3 | 2 |
| `consume_slist(ys)` (stops: `old_rc == 3 ≠ 1`) | 2 | 2 |
| later: result released (stops at shared `H`) | 1 | 2 |
| later: caller releases `ys` — `H` → 0, descends to `D`, `old_rc == 2 ≠ 1`, stops | freed | **2** |

`D` and its element retain a reference nothing can discharge: a per-call deep
leak proportional to `|ys|`, compounding across chained `sconcat` calls. That
matches 0835's own signature — hand-chained `sconcat` is fine, freshly-built
cells consumed in the same expression die around six cells, and the `derive`
ceiling moves with arity.

This is the S116 ruling-2 releasing-owner inventory's **second** row (known
runtime protocol trees → their intrinsics `consume_*` owner), not the first
(generated lexical ownership → backend type-directed glue). **The backend
consumer migration does not reach `sconcat` at all.**

## Proposed resolution

1. `/testing` lands FIXME 0835's repro A and repro B as failing-not-ignored
   cells with **process-abort guards** (the failure is a SIGABRT; a bare value
   assertion takes the harness down), per 0835's own request 1.
2. `/qa` attributes with this falsification recipe: run repro B under
   `CRANELISP_RC_STATS=1` and plot `allocs - deallocs` against the number of
   `step` applications.
   - residual growing with `|ys|` per `sconcat` call ⇒ the marshal /
     `consume_slist` asymmetry above; re-own to `/dev`(runtime) — a `/design`
     ruling on `consume_*`'s deep-inc contract is likely owed first;
   - residual proportional instead to *type nesting depth*, or vanishing when
     the backend consumers migrate ⇒ the transitive-discharge class, and it
     stays with `/dev`(backend).
3. Record the outcome in 0835 and in `s118-test-plan.md` §4, and tell `/sprint`
   whether Track B item 1's "0835 first" ordering still applies.

## Impact on the Track B wave

Slice order is **unaffected**: 0835 is not a precondition of any other slice.
`design/backend/transitive-drop-glue.md` §7.2 records the slice as
attribution-gated, and the wave proceeds S0 → S1 → S3 → S4 → S5 → deletion if
attribution lands outside the backend. Ruling 1(d)'s "0835 first" was an ordering
*within the transitive-discharge class*, which 0835 may turn out not to join.

## Context

Filed by `/design`(backend) during the S118 Phase-3 refresh of
`transitive-drop-glue.md`, while reconciling the arch-ruled migration order
against the committed test corpus. The mechanism above is read from source, not
measured — hence the falsification recipe rather than a re-attribution.
