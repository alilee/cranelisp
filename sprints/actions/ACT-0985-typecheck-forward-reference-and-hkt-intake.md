---
id: ACT-0985
title: Assess declaration forward-reference and higher-kinded dispatch leads
status: deferred
priority: required
from: design
to: qa
sprint: 122
filed_at: 2026-09-22
refers_to:
  - design/typecheck/typecheck.md
  - design/typecheck/hkt.md
  - spec/05-definitions.md §5.13.1
  - crates/cranelisp-typecheck/src/traits/impl_check.rs
---

## S122 disposition (user-approved 2026-09-30)

Under the [approved S122 disposition](../../tests/plan/s122-evidence-delta.md#final-disposition-proposal-2026-09-30):

- **Carried to S123 (K5, N3).** First deferral.

## Confirmed: an impl body refused for an impl declared later (qa, 2026-09-30)

The forward-reference lead has a confirmed batch face, found while checking
ACT-1034's C1 control (`.local/qa-s122-6b/sentinel/c1.py`). The probe used a
copy of `target/debug/cranelisp` built after `88bbbd12`, with the
primitives-only prelude.

```clojure
(deftype (Opt a) Nope (Yep [:a v]))
(deftrait Size (size [self] Int))
(impl Size (Opt a) (defn size [o] (match o [Nope 0 (Yep x) (size 42)])))
(impl Size Int (defn size [n] n))
(defn main [] (Pure (size (Yep 3))))   ; §5.13.1 requires 42
```

- `--run` and `--link` refuse it:
  `impl of trait Size for user/Opt: method size does not conform: no impl of trait user/Size for type primitives/Int`.
- **Control:** the same file with `impl Size Int` first exits 42 in both modes.
  The two files differ only in declaration order.
- §5.13.1 lets an implementation in one cluster reference definitions that
  appear later, and a batch file is one cluster. The REPL refusal is correct,
  because each REPL input is its own cluster (§5.13.2).
- **Class:** `wrong-reject`. Hypothesis: impl conformance is checked against
  the impl registry as it stands at that impl's source position
  (`traits/impl_check.rs`). Refuted if both impls are registered before
  either body is checked.
- **Allocation:** `test` commits a failing, un-ignored `--run`/`--link` cell in
  `tests/spec_05_definitions.rs` citing
  `// spec: spec/05-definitions.md §5.13.1`, with the impl-first order as the
  passing control. It is a discovered defect, so the RED lands now under
  METHOD §2.2. The carry defers the correction, not the reproduction.

## A REPL face: two implementations in one `begin` (qa, 2026-11-18)

`target/debug/cranelisp` at `1a3ab46e`. Fixture: T-Q7-d of the
[S124 evidence delta](../../tests/plan/s124-evidence-delta.md#91-type-concreteness-item-1),
an `(impl Size (Box :Size a) …)` and an `(impl Size (Opt :Size a) …)` whose
bodies each dispatch to the other.

| Input | Observed |
|---|---|
| REPL, `(begin <Box impl> <Opt impl>)` | refused at the `Box` impl: `no impl of trait user/Size for type user/Opt` |
| REPL, `(begin <Opt impl> <Box impl>)` | refused at the `Opt` impl: `no impl of trait user/Size for type user/Box` |
| File, `Box` impl first, with or without the `begin` | typecheck accepts; refused at codegen (ACT-1034) |
| File, `Opt` impl first | refused: `no impl of trait` |

- One REPL input is one cluster (§5.13.2), so §5.13.1 admits both orders.
  The `begin` is the only way to enter the pair at the REPL.
- The file accepts one order where the REPL accepts neither. The hypothesis
  above does not explain the accepted order; `dev`(typecheck) probes it
  before implementing.
- **Cells:** `spec_07_traits::s124_q7_d_box_first_repl` and
  `s124_q7_d_opt_first_repl`. They are constructed as allocated and stop at
  this refusal. Row T2's completion includes them reaching their value
  clause.

## Corrected by T2; one shape held on a requirement question (qa, 2026-11-18)

`target/debug/cranelisp` built from `24c42430`. The batch guard
`spec_05_definitions::impl_body_uses_impl_declared_later_in_cluster` and
T-Q7-d's REPL and `Opt`-first legs pass.

One shape is still refused. With a second form for the same pair between the
two implementations, the first body is checked before `Size Int` registers:

```clojure
(impl Size (Opt a) (defn size [o] (add-i64 1 (size 42))))
(impl Size (Opt a) (defn size [o] (add-i64 2 (size 42))))
(impl Size Int (defn size [n] n))
(defn main [] (Pure (size (Yep 3))))
```

| Leg | Observed |
|---|---|
| Subject | refused at the first form: `no impl of trait p/Size for type primitives/Int` |
| Control: the first form removed | 44 |
| Control: `impl Size Int` first | 44 |
| Control: a first form whose body dispatches nowhere | 44 |

- **No cell is allocated.** The specification states replacement for an
  `impl` re-entered in a later input (§5.4.5) and does not say whether two
  forms for one pair in one cluster are a replacement or an error. Under
  replacement the subject is a wrong reject; under an error it is refused
  with another message. The question is with `spec`.
- `design`(typecheck) records the shape as an
  [open item](../../design/typecheck/traits.md#11-open-items), to repair on a
  failing cell.

## Request

Classify three source-read leads from the typecheck design reconciliation before
changing behavior or treating existing tests as authority:

- Declaration forward references: the master design's open items contrast
  spec/05-definitions.md section 5.13.1 and spec/08-modules.md section 8.10.4
  with `tests/spec_09_macros.rs::macro_expanded_begin_impl_neg_before_deftype_is_rejected`.
  That test requires rejection when expansion places an impl before its type.
  Reconcile the governing scope with spec; seek a user ruling only if required
  meaning remains unsettled.
- Result-only constructor variables: the HKT design's open questions record
  `find_hkt_param_index` defaulting to parameter zero when no parameter applies
  the constructor variable. Assess the admissibility and dispatch of a method
  such as `(pure [:a x] (f a))` against spec/03-types.md section 3.7.6.
- Primitive identity: the HKT design records Case 2 rejection comparing the
  written spelling against Int/Bool/String/Float. Assess equivalent qualified
  or renamed references against the same kind requirement.

## Completion evidence

These are unexecuted leads, not confirmed or closed defects. QA determines the
minimal discriminating reproductions and controls, routes requirement ambiguity
to spec, and attributes confirmed failures before implementation. Preserve any
confirmed defect as an unignored spec-traced test; record each lead's disposition.

Provenance: design session `511c3863-4a8b-4ac4-8288-7c24e9d964ac` inspected
`traits/registry.rs`, `traits/impl_check.rs` and the macro test above. Sprint
reopened those source loci before filing; no runtime reproduction was run.
