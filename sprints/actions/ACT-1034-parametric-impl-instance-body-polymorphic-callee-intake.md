---
id: ACT-1034
title: A parametric impl's method instance cannot call a polymorphic callee instantiated through the impl's type variable
status: resolved
priority: required
from: qa
to: qa
sprint: 122
filed_at: 2026-09-30
refers_to:
  - spec/07-traits.md §7.3.3
  - spec/05-definitions.md §5.4.3
  - repl/spec/05-error-presentation.md §5.5
  - crates/cranelisp-backend/src/compiler/apply.rs::compile_direct_call
  - design/arch/fixmes/0915-codegen-diagnostic-exposes-mangled-doubled-internal-subjects.md
  - tests/spec_07_traits.rs
  - tests/plan/s122-evidence-delta.md
---

## Observation

Observed by QA on 2026-09-30 with `target/debug/cranelisp` built after
`88bbbd12`, with no source edits since. The prelude was
`tests/fixtures/preludes/primitives-only.cl`. Each probe ran in a fresh
directory. The lead came from `training`'s Phase-6a assessment.

```clojure
(deftype (Opt a) Nope (Yep [:a v]))
(deftrait Size (size [self] Int))
(impl Size (Opt :Size a)
  (defn size [o] (match o [Nope 0 (Yep x) (add-i64 1 (size x))])))
(impl Size Int (defn size [n] n))
(defn main [] (Pure (size (Yep (Yep 3)))))   ; §7.3.3 requires 5
```

- Every mode refuses it:
  `codegen failed for p/(p/Size.size$p/Opt [(p/Opt (p/Opt primitives/Int))] primitives/Int): … undefined function: Size.size$p/Opt`.
  The REPL session survives the error.
- The spec's canonical §7.3.3 and §5.4.3 example has this shape: the impl
  body calls `(show x)` on its payload. Search tier 2 of §7.3.3 satisfies
  `a = (Opt Int)` through the polymorphic impl itself.
- The fault is also present in a release binary built on 2026-09-29 at 09:31,
  before `e4062202`.
- In the table below, the impl is declared before `impl Size Int` so that
  ACT-1035 (a REPL crash, closed S123 at `91acf712`) could not fire.

| Cell | Inner call from the impl-method instance | REPL | `--run` | `--link` |
|---|---|---|---|---|
| A1 | `size` at `(Opt Int)`, the same impl | refused | refused | refused |
| A2 | `size` at `(Box Int)`, a different constrained impl | refused | refused | refused |
| A3 | generic free `(k7 x)` at `a = Int`, in an *unconstrained* `(Opt a)` impl | 7 | refused (`undefined function: k7`) | refused |
| C3 | the generic free function `twice` calls `size` at `(Opt Int)` | refused | 8 | 8 |
| C1 | `size` at `Int` (a monomorphic target) | not constructible (below) | 42 | 42 |
| C2 | the same body in a monomorphic `(impl Size (Opt Int))` | 42 | 42 | 42 |

- **C1 needs `impl Size Int` first.** Re-probed on 2026-09-30
  (`.local/qa-s122-6b/sentinel/c1.py`).
  - With the parametric impl first, every mode refuses the body:
    `no impl of trait user/Size for type primitives/Int`. In batch this is
    the wrong-reject recorded on
    [ACT-0985](ACT-0985-typecheck-forward-reference-and-hkt-intake.md).
  - With `impl Size Int` first, the REPL crashed (ACT-1035, fixed S123), so
    C1 had no REPL leg. The earlier REPL entry of 42 did not reproduce.
- **Controls.**
  - The fault does not need the constraint: A3 is unconstrained.
  - It does not need self-recursion: A2 calls another impl.
  - A monomorphic target (C1) and a monomorphic impl (C2) both work.
  - The same callee at a concrete type works: `(ident 7)` in the body
    returns 7.
- **Mode divergence.** A3 and C3 diverge in opposite directions. The S124
  attribution below shows the variable is cluster shape, not mode.

## A third face: the implementation's own instantiation (qa, 2026-11-17)

Observed at `4b58ab93`, no prelude, `--run`; the first also at the REPL.

| Program | Required | Observed |
|---|---|---|
| `(impl Len (L a) (defn len [l] (match l [LNil 0 (LCons h t) (add-i64 1 (len t))])))` over a two-element `(L Int)` | 2 | `undefined function: Len.len$p/L` |
| `(impl Cont (Opt a) …)` whose `describe` is `(add-i64 4 (size o))`, either member order, or imported | 5 | `undefined function: Cont.size$p/Opt` |
| Control: the same two members in an impl for a type with no parameters | 5 | 5 |

- In the first, typecheck publishes the instance at `[(L Int)]` and the
  call inside it is not redirected to that key. In the second, the
  sibling's instance is not published.
- The designed correction covers both
  ([monomorphisation §3.10.3](../../design/typecheck/monomorphisation.md#3103-recursion-through-dispatch),
  the chain's equal-key row). Cells: T-1034-d and T-1034-e
  ([evidence delta §2.3](../../tests/plan/s124-evidence-delta.md#23-conditions)).

## A fourth face: re-entry at another instantiation (qa, 2026-11-17)

Under S124-Q7 as re-ruled B, a dispatch from an implementation's body to
that implementation at another instantiation is an ordinary dispatch.
Observed at `4b58ab93`, no prelude, `--run`:

| Program, inside `(impl Size (Opt :Size a) …)` unless stated | Required | Observed |
|---|---|---|
| A `Nope` arm of `(size (Yep 7))`, reached from `(Opt Int)`, `(Opt Bool)` or `(Opt (Opt Int))` | 7 | `undefined function: Size.size$p/Opt` |
| A `Nope` arm of `(size (Yep (Yep 7)))`, reached from `(Opt Int)` | 7 | the same |
| A sibling `describe` as `(add-i64 4 (size (Yep 0)))` in `(impl Cont (Opt a) …)` | 5 | `undefined function: Cont.size$p/Opt` |
| Two implementations that dispatch to each other, `Box` declared first | 4 | `undefined function` |
| Control: the `Nope` arm as `(wsize (Yep 7))` through `(defn wsize [:Size x] (size x))` | 7 | 7 |
| A growing body, `(size (Yep o))`, demanded by `main` | a type error (spec §3.10) | refused at codegen as `undefined function` |

- The last row is not a legal program. Its fault is the refusing stage and
  message; the chain of the designed correction raises the type error.
- Cells: T-Q7-a to T-Q7-d and F-PR to F-PR-4
  ([evidence delta §9.1](../../tests/plan/s124-evidence-delta.md#91-type-concreteness-item-1)).

## Attribution (qa, 2026-11-16, S124 Phase 3, at `4b58ab93`)

The measurements and their limits are in the
[S124 evidence delta](../../tests/plan/s124-evidence-delta.md#2-act-1034--attribution).

- **Owner: typecheck. Confirmed at the producer seam.** For each failing
  shape, typecheck's per-cluster callable list (`CRANELISP_OWNERSHIP_TRACE=1`)
  contains the outer instance and no instance for the inner call. The stated
  refutation ("typecheck publishes a minted-instance key for the inner call
  and the backend misses it") did not occur. The backend's refusal of the
  slotless template is the consumer working as designed.
- **Two omissions in successor discovery inside a minted instance.**
  - *Dispatch hop (A1, A2, C3).* A trait-dispatched call inside a minted
    instance, whose target is a parametric impl template, is never demanded.
  - *Free-function hop (A3).* A call to a generic free function inside a
    minted impl-method instance is not demanded when the callee is a template
    of the same cluster. It is demanded when an earlier cluster published the
    callee.
- **No `src/` part: the REPL/batch difference is cluster shape.** The REPL
  leg enters one form per turn and the batch leg is one cluster. With the
  cluster shape held equal, the REPL and `--run` agree in all four cells
  (six shapes each). A3 fails exactly when `k7` shares the caller's cluster.
  C3 fails exactly when `twice` was published by an earlier cluster; in one
  cluster `twice` settles concrete, so no instance-in-instance arises.
- **Refuted if** two runs with the same cluster structure differ between the
  REPL and `--run`, or a failing shape's trace lists the inner instance.
- **Class:** `carrier-loss` stands; the locus is typecheck's instance
  successor discovery (`traits/monomorphise.rs`, `program/mono_collect.rs`).
  `design`(typecheck) names the exact site.

## §5.5 frame witness

- The refusal is a public codegen error. It has a doubled `codegen error at`
  prefix, a module-doubled subject (`p/(p/…)`) and a `$` instance mangle.
- It therefore fires the falsifier of FIXME 0915's K9 carry ("any public
  codegen error").
- **Routing:** `sprint` returns that carry to the user; see the
  [evidence delta](../../tests/plan/s122-evidence-delta.md#phase-6a-intake-training-and-docs-leads-2026-09-30).

## Evidence allocation

- **`test` (allocated now):** commit A1, A2, A3 and C3 as failing, un-ignored
  cells in `tests/spec_07_traits.rs`.
  - Cite `// spec: spec/07-traits.md §7.3.3`.
  - Use a provisional `class=carrier-loss`.
  - Run every mode, with C1 (batch only) and C2 as passing controls.
    Committed as `parametric_impl_instance_calls_monomorphic_target_batch_control`
    and `monomorphic_impl_same_body_all_modes_control`.
  - **Now constructible (S123):** add the REPL leg to C1, with `impl Size Int`
    first. If it fails, `qa` attributes it before it joins this filing.
  - Declare the parametric impl before `impl Size Int`.
  - Assert the value in each mode, and assert that no `undefined function`
    text appears.
- **`test` (S124):** the cluster-shape cells T-1034-a to T-1034-c of the
  [S124 evidence delta](../../tests/plan/s124-evidence-delta.md#2-act-1034--attribution),
  so each mode observes both publication states.
- **`dev`:** the unit row at the producer seam `design` names. The fix lands
  with the unit test.
- **Coverage attribution.**
  - The `TB-24` cells register a constrained impl whose body returns a
    constant (`(defn dp [x] 7)`).
  - No cell discharges the constraint inside the body or instantiates the
    impl through another parametric instance.
  - `qa` restores the §7.3.3 and §5.4.3 bands when the cells pass.

## Disposition

Fix or carry is the user's decision under METHOD §2.4. QA retains this intake.

## Completion evidence

A1, A2, A3 and C3 go RED for their intended reason, then GREEN after the
correction in every mode, with C1 and C2 still passing. QA restores the
§7.3.3 and §5.4.3 bands.

## Resolved (qa, 2026-11-20)

Every cell of this filing passes in the full run at `b72742f7`: the five
S122 cells (A1, A2, A3 and the two monomorphic controls) and the 27 cells
named `s124_1034_*`. A1 gives 5 by hand under `--run` and linked on the
binary built from `3c5e41ca`. Each was RED on its value when committed (evidence delta §2 and §9.1).
`qa` did not identify the correcting commit.

`qa` restored the §7.3.3 and §5.4.3 bands. The standard library's new
`Eq`, `Ord` and `Display` implementations for `Option`, `Result` and `Pair`
have this filing's shape and compile.

Owed before the file is deleted: `test` stamps the cells' `// defect:`
lines with `fixed=` and puts their comments in the past tense.
