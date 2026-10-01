---
id: ACT-1034
title: A parametric impl's method instance cannot call a polymorphic callee instantiated through the impl's type variable
status: open
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
  [ACT-1035](ACT-1035-repl-concrete-impl-crashes-after-later-parametric-impl-intake.md)
  cannot fire.

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
  - With `impl Size Int` first, the REPL crashes (ACT-1035).
  - So C1 has no REPL leg until ACT-1035 is fixed. The earlier REPL entry of
    42 did not reproduce.
- **Controls.**
  - The fault does not need the constraint: A3 is unconstrained.
  - It does not need self-recursion: A2 calls another impl.
  - A monomorphic target (C1) and a monomorphic impl (C2) both work.
  - The same callee at a concrete type works: `(ident 7)` in the body
    returns 7.
- **Mode divergence.** A3 and C3 diverge in opposite directions.

## Attribution

- **Status: provisional.** The symptom and its discriminator are established.
  The producer mechanism has not been observed.
- **Discriminator:** the calling body is an instance minted from a
  *parametric* impl method, and the callee is polymorphic, so its instance
  must be minted with type arguments derived from the impl's substitution.
- **Consumer seam observed.** The call reaches the non-resolver tail of
  `compile_direct_call`, where the fetched entry has no GOT slot. The name the
  consumer reports is the unmangled template (`Size.size$p/Opt`, `k7`).
- **Hypothesis:** the call site in the minted body is carried to the slotless
  template rather than to a minted instance. This is the `carrier-loss` shape,
  as in S112 R2. The likely producer is typecheck's minting of impl-method
  instances; the REPL/batch divergence may place part of it in `src/` instance
  driving.
- **Refuted if** typecheck publishes a minted-instance key for the inner call
  of A1 and the backend misses it. The owner would then be backend or `src/`
  emission.

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
    and `monomorphic_impl_same_body_all_modes_control`. C1 gains its REPL leg
    with ACT-1035's correction.
  - Declare the parametric impl before `impl Size Int`.
  - Assert the value in each mode, and assert that no `undefined function`
    text appears.
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
