---
number: 0347
target: /design
filed_by: /dev
filed_at: 2026-06-14
sprint_filed: 82
refers_to: crates/cranelisp-backend/src/compiler/control_flow.rs:709 (span-derived __lambda name), design/backend/ (monomorphisation of pure-parametric polymorphic fns), design/typecheck/inference.md §"Cross-Defn Generalization Timing (FIXME 0344)", design/arch/fixmes/0344-typecheck-vec-reduce-polymorphic-accumulator-misinference.md
status: open
---

# Backend monomorphisation of a pure-parametric polymorphic fn breaks when the fn (a) contains a lambda or (b) is a recursive fold — exposed by the 0344 typecheck fix

## Issue (S82 Wave 2 /dev typecheck finding)

The 0344 typecheck fix (generalize-before-cross-defn-use, landed S82 W2 in
`program.rs::check_form_body_single_defn` + the multi-sig site) makes a defn
that was previously monomorphised-in-place (via the shared Pass-2 substitution
of its single concrete caller) stay genuinely **polymorphic** when it is
checked before its caller. That is the correct inference (it is what fixes the
`vec-reduce` accumulator over-unification). But it pushes such fns through the
backend's **monomorphisation** path (the Additive `finalize` mono-marking,
`program.rs` ~1189: polymorphic `UserFn` + `ast` ⇒ marked for mono), and that
path has two latent defects the prior over-unification was masking:

1. **Duplicate `__lambda` definition when a lambda-bodied polymorphic fn is
   monomorphised.** `cranelisp-backend` names a lambda function by its source
   span — `format!("__lambda_{}_{}__", span.start, span.end)`
   (`control_flow.rs:709`). The name is **span-derived, not
   monomorphisation-aware**: two mono copies of the same source fn emit the
   same `__lambda_<start>_<end>__` and the linker rejects the second with
   `Duplicate definition of identifier: __lambda_…__`. Surfaced as 4 example
   regressions (`13-higher-order.cl`, `21-hello-io.cl`, `23-io-sequence.cl`,
   `27-lazy-seq.cl`) the moment higher-order fns stopped being
   monomorphised-in-place.

2. **A monomorphised recursive fold returns the wrong runtime value.** The
   0344 **e2e** guard (`tests/spec_04_expressions.rs::polymorphic_accumulator_fold_does_not_over_unify`)
   now **type-checks** (the typecheck defect is fixed — the unit guard in
   `cranelisp-typecheck` is green and asserts the exact scheme
   `(Fn [(Fn [b a] b) b (Vec a)] b)` + `(reduce add-i64 0 [1 2 3])` ⇒ Int),
   but the linked program **exits 0 instead of 6**: the monomorphised
   `reduce`/`reduce-loop` fold does not execute its accumulation. The scheme is
   correct at the typecheck seam; the wrong value is produced downstream in
   mono/codegen, not in inference.

## Interim mitigation already in place (S82 W2 /dev)

To keep the workspace suite green at exactly the 14 documented known-defect
guards, the 0344 typecheck writeback is **gated to skip lambda-bodied defns**
(`expr_contains_lambda(defn.body())` in `program.rs`) — those keep the prior
monomorphise-in-place behaviour, sidestepping defect (1). The fold case has no
lambda, so the **unit** guard (the typecheck contract) is satisfied; the **e2e**
guard stays red on defect (2), carried forward as a known guard (it improved
from a type error to a runtime-wrong-value — same guard, still owned downstream).

The lambda gate is a **typecheck-side band-aid for a backend limitation** and
should be removed once defect (1) is fixed in the backend.

## Proposed resolution

Owning surface: **backend** (`/design` for backend, then `/dev`).

1. Uniquify the lambda codegen name per monomorphic instantiation — append the
   mono key (the concrete type substitution / specialisation suffix) to
   `__lambda_<start>_<end>__`, the same way the enclosing mono fn is suffixed,
   so N mono copies of one source fn get N distinct lambda symbols. Then the
   typecheck-side `expr_contains_lambda` gate can be deleted (re-enabling the
   0344 generalization for higher-order fns).

2. Investigate the monomorphised recursive-fold wrong-value (defect 2): verify
   the mono specialisation of a self-recursive helper (`reduce-loop` calling
   itself) threads the accumulator correctly and that the GOT slot / call target
   for the recursive self-reference resolves to the specialised body. Likely
   related to mono of a fn whose recursion-name binding stays `mono(fn_type)`
   (the 0344 design KEEPS monomorphic recursion deliberately).

## Operational implication / Context

The 0344 **typecheck** half is complete and guarded by a green unit test. The
0344 **e2e** guard and the (now-prevented) higher-order example regressions are
the backend half. Until the backend half lands, the lambda gate stays. Removing
the gate without fixing defect (1) re-reds the 4 examples; fixing defect (1)
without (2) still leaves the 0344 e2e red.
