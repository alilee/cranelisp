---
id: ACT-1077
title: A local named like `bind` or a platform function leaves an eligible bind chain elsewhere in the same definition sequential
status: open
priority: advisory
from: qa
to: qa
sprint: 124
filed_at: 2026-11-18
refers_to:
  - spec/10-io.md §10.12.1
  - design/int/bind-chain-analysis.md §3.1
  - design/int/bind-chain-analysis.md §7
  - src/bind_chain_analysis.rs::collect_binders
  - tests/plan/s124-evidence-delta.md
---

## Observation

`qa`, on the debug build of `84719eb6`, 2026-11-18, `--run --no-cache`, the
`poll-pool` platform, best of three runs. Reported by `design`(int) from the
design.

`B` is REPRO-0981's body: two 300 ms `poll-read`s on tokens 1 and 2, both
results used. `BD` makes the second depend on the first.

| Leg | Definition | Observed |
|---|---|---|
| Overlap reference | `(defn f [d] B)` | 324 ms |
| Serial reference | `(defn f [d] BD)` | 628 ms |
| Subject | `(defn f [d] (if (eq-i64 d 0) (let [bind 1] (Pure bind)) B))` | 623 ms |
| Subject | the same with the local spelled `poll-read` | 624 ms |
| Control | the same with the local spelled `then` | 322 ms |

Every leg exits 0 with the right value.

## Classification: a defect, low harm

- **Requirement.** Spec §10.12.1: when a pair of bindings is data
  independent and commutative, the compiler inserts a `Par` node. The local
  is bound in another arm and cannot reach the chain, so the pair is
  eligible.
- **Face.** Lost overlap only. The sequential program is the correct one,
  so no value, order or memory fault follows.
- **Class:** `wrong-scope-lookup`. The pass's binder set is collected once
  per definition and ignores nesting.
- **Known as built.** [Bind-chain analysis](../../design/int/bind-chain-analysis.md)
  §3.1 states the over-approximation and §7 records the missed rewrite. It
  entered with ACT-1065's correction (`32e434dc`), which is sound.

## Attribution

- **Mechanism, stated by the design and confirmed by a control.** The
  control differs from the subject only in the local's spelling.
- **Owner:** `src/` (`design`(int) for the scope threading §7 names).
- **Refuted if** the `then` control is serial, or the subject overlaps.

## Evidence allocation

`test`, in `tests/spec_10_io.rs` beside REPRO-0981, reusing its sampling
helper and its two references: the `bind` subject and the `then` control,
`--run`. The subject's regime equals the overlap reference's, under the
[wall-clock rule](../../tests/plan/PLAN.md#traceability-and-authoring).
Cite `// spec: spec/10-io.md §10.12.1` and
`// defect: class=wrong-scope-lookup locus=src/bind_chain_analysis.rs::collect_binders found=S124 owner=/dev`.

This is acceptance evidence for §10.12.1 in this implementation, which runs
`Par` branches concurrently. One cell is allocated: the `poll-read` spelling
goes through the same binder set and adds no discrimination.

## Disposition

Correct or carry is the user's decision
([METHOD §2.4](../METHOD.md#24-deferral)). It ends no program and refuses
none. `qa` retains this intake.

## Completion evidence

The subject is serial before the correction and overlaps after it; the
control overlaps throughout.

## A regression S124 caused (qa, 2026-11-19, `d30c70e9`)

- **Measured.** The subject overlaps (310 to 313 ms) on the release binary
  of 2026-11-18 00:11, the W2 tree, and is serial (628 to 630 ms) on
  `d30c70e9`. The `then` control and both references agree on the two
  binaries ([evidence delta §14.10](../../tests/plan/s124-evidence-delta.md#1410-no-decay)).
- **Consequence.** Under the *no decay*
  [delivery principle](../METHOD.md#delivery-principles) the correction
  is owed in S124. The priority above predates that principle.
- **Limit.** The earlier binary is not the opening tree and its commit is
  not pinned.
