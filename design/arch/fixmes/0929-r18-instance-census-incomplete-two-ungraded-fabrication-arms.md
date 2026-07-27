---
number: 0929
target: /design
filed_by: /qa
filed_at: 2026-07-27
sprint_filed: 119
refers_to: design/arch/safety-invariants.md §4 rows R17/R18;
  crates/cranelisp-typecheck/src/ownership/fixpoint.rs:221;
  crates/cranelisp-backend/src/drop_glue.rs:398;
  crates/cranelisp-types/src/heap.rs:310-334;
  crates/cranelisp-typecheck/src/program/support.rs:321;
  design/backend/non-concrete-release-contract.md §3.2;
  design/typecheck/non-concrete-producer-obligations.md §3;
  tests/plan/s119-test-plan.md §3.7 (the NC-2 census allow-list)
status: open
---

# R18's instance census is incomplete: two fabrication arms live outside both design censuses, and one carries an unproven soundness claim in its rustdoc

> **`/arch` disposition (2026-07-27, S119 step-back ruling) — asks 1–3
> DISCHARGED; ask 4 RULED; residue re-targeted to `/design`(backend).**
>
> - **Asks 1+2 discharged**: `safety-invariants.md` §4 R18 now carries sites
>   1–5 with per-site grades and owners (fixpoint.rs:221 = ungraded narrowing
>   owing its P25 check, `/dev`(typecheck) NC-3(b); drop_glue.rs:398 =
>   located-refusal disposition, `/dev`(backend); context.rs:280 = Type-side
>   laundering, rides R17's declaration-channel cure; fn_compiler.rs:1214 =
>   dead-arm spelling, low; the int trio = grading owed by `/design`(int)),
>   and names the two model sites as the required spelling. R17 now records
>   the declaration channel as a structural feeder and NC-5 as the arm-flip
>   precondition.
> - **Ask 3 answered**: `/qa`'s recommendation ACCEPTED — no sealing;
>   census-as-enforcement (NC-2 families A+B); residual grade
>   `asserted-with-a-named-falsifier` once NC-2 lands with its detection
>   proof. Recorded on the R18 row.
> - **Ask 4 ruled — the split**: the *derivation seam* is a `cranelisp-types`
>   decision and is ruled — ctor field-type materialisation for category/glue
>   purposes delegates to the types-owned refusing projection
>   (`heap.rs::ctor_field_concrete_types`) or an instantiation-substituting
>   sibling landed beside it in `heap.rs` (an addition there is pre-approved
>   in shape; exact signature via the ordinary FIXME `target: /arch` if
>   needed). The *carrier shape* (`CtorField { ty: ConcreteType }` vs
>   instantiation-keyed materialisation, keying, caching) is backend-interior
>   (`CtorMeta` is `pub(crate)`) and is `/design`(backend)'s to rule inside
>   the release-contract window — hence this FIXME's re-target.
> - **This file stays open as the NC-2 allow-list citation anchor** until the
>   per-site dispositions land; the remaining design decision is the
>   `/design`(backend) CtorMeta ruling above.

## Issue

R18 ("No fabricated concreteness") enumerates three measured instances:
`rc_emission.rs:493`, `fn_compiler.rs:1287`, `mono_expr.rs:836-841`. A `/qa`
source census at HEAD (S119, the user's negative-coverage finding) found the
full discard-and-substitute population on `ConcreteType::from_type` is **four
fabricating arms plus two correct refusal sites**, and two of the four appear
in NEITHER the release contract's censuses NOR the producer obligations NOR
R18's row:

1. **`crates/cranelisp-typecheck/src/ownership/fixpoint.rs:221`** —
   `ConcreteType::from_type(t).unwrap_or(ConcreteType::String)` when seeding
   per-param ownership facts. The enclosing rustdoc claims soundness on one
   axis only: "falls back to a non-scalar placeholder (`String`) — never
   mis-classified as `Copy` (sound: a non-`Copy` param seeds `Borrowed`)."
   That is a **narrowing rationale with no cited check** (Principle 25): the
   claim protects the Copy⊑Borrowed edge but says nothing about whether a
   residual-typed param may legally *stay* at `Borrowed` (below ⊤ `Owned`)
   through the fixpoint — exactly the elide-an-inc consequence class R1/R18
   exist for. Needs grading: either the arm gains its P25 check (and a
   fail-on-revert unit row, `s119-test-plan.md` §3.7 NC-3(b)) or it is ruled
   legitimate-with-proof and joins the model list below.
2. **`crates/cranelisp-backend/src/drop_glue.rs:398`** —
   `args.first().cloned().unwrap_or(ConcreteType::Int)` in `ctor_shapes`'
   Vec arm: a Vec glue request whose elem type argument is absent mints
   Int-elem glue (frees heap elements as scalars if the arm is ever reached
   with a heap elem unstated). If the arm is believed dead, that is
   "graded by inspection" — the §Assurance failure state; the disposition
   should be a located refusal (the `:497-505` pattern) or a proof.

## Extension (2026-07-27, coordinator follow-up, verified at source): the Type-side laundering family and the declaration channel

The `from_type` census pattern is structurally blind to fabrications that
happen BEFORE the boundary and then *pass* `from_type` — laundered
concreteness. Verified instances:

3. **`crates/cranelisp-backend/src/compiler/context.rs:280`** —
   `field_types.get(i).cloned().unwrap_or(Type::Int)` in
   `extract_constructor`: a ctor whose `field_count` exceeds its scheme's
   params fabricates `Type::Int` field types. Same expression exposes the
   **declaration channel**: `CtorMeta`/`CtorField` is materialised from the
   ctor *declaration's* scheme, so a polymorphic product's field type is
   `Type::Var(a)` permanently — nothing substitutes concrete args at use
   sites — and `signature_heap_category`'s `Err ⇒ Mixed` arm (R17's seam)
   licences the guarded-RC path off it. Two consequences for standing
   instruments: the NC-1 slot-gate sweep is structurally blind to this
   channel (it quantifies over slotted entries' schemes), and **R17's
   arm-flip criterion (census reads zero) is unreachable while this channel
   stands** — every polymorphic-ctor field categorisation is permanent
   census traffic. Plan cell NC-5 (`s119-test-plan.md` §3.7) asserts the
   seam invariant design-neutrally; the **representation question** —
   `CtorField { ty: ConcreteType }` making the state unconstructable, with
   materialisation instantiation-keyed — is `/design`(backend)'s to rule
   inside the release-contract window. Ask 4 routes it.
4. **`crates/cranelisp-backend/src/compiler/fn_compiler.rs:1214`** —
   `variable_types.get(name).cloned().unwrap_or(Type::Int)`: a **defensive
   dead arm** (the preceding filter guarantees `Some`); unreachable by
   local construction, but the wrong spelling — `expect`/`filter_map` says
   what is true. Low severity; grade accordingly.
5. **Int-layer result/display defaults** — `src/eval.rs:586`,
   `src/repl/commands.rs:632`, `src/pipeline.rs:133`: absent display/expr
   type defaults to `Type::Int`, and the fabricated type flows toward the
   result-release protocol (R15's `(i64, Type)` narrow-once seam). Whether
   a heap-typed result can ever reach these arms with `display` absent is
   exactly the ungraded-inspection question; needs grading, not assumption.

All five are pinned in NC-2's family-B allow-list citing this FIXME.

## The model sites — worth naming ON the R18 row

Two sites handle `NotConcrete` correctly and should be cited by the register
row as the required spelling, so the row teaches the fix, not only the
prohibition:

- `crates/cranelisp-typecheck/src/program/support.rs:321` — explicit
  `ViewBuildError::NotConcrete` match for a documented legitimate case.
- `crates/cranelisp-types/src/heap.rs:310-334` (`ctor_field_concrete_types`)
  — `.map(|t| from_type(t).ok()).collect::<Option<Vec<_>>>()`: one residual
  field refuses the whole ctor, documented "conservatively ineligible".
  (An earlier read of this site as a discard was wrong — the `Option`
  collect makes it a refusal.)

## The structural-closure question (asked, with a recommendation)

`ConcreteType`'s variants are `pub`, so `from_type`'s "the ONLY way to obtain
a `ConcreteType` from a `Type`" rustdoc claim is enforced for conversion but
not against direct literal construction — and every live fabrication IS a
direct literal in `unwrap_or` position. `/qa` recommendation: do NOT seal the
variants (exhaustive matching across backend is load-bearing and legitimate
literal construction exists, e.g. known-Int contexts); adopt the NC-2
fabrication census (`s119-test-plan.md` §3.7 — pinned allow-list, every entry
carrying an open-defect citation, new sites RED in their own change-set) as
the enforcement mechanism, and grade the residual
**asserted-with-a-named-falsifier** on the R18 row (falsifier: the census
pattern firing, or a fabricating literal outside `unwrap_or` position found
by the next census sweep). Yours to accept or overrule.

## Ask

1. Extend R18's instance list with sites 1–5 (or rule any legitimate, with
   the proof cited on the row). Site 3's declaration channel also belongs on
   the R17 row: its arm-flip end state is unreachable while the channel
   stands.
2. Name the two model sites on the row.
3. Answer the structural-closure question; if census-as-enforcement is
   accepted, record the residual grade on the row.
4. Route dispositions to owners: `/design`/`/dev` typecheck for
   fixpoint.rs; `/design`/`/dev` backend for drop_glue.rs, and for the
   `CtorMeta` representation question (site 3 — `CtorField.ty:
   ConcreteType` vs instantiation-keyed materialisation, ruled inside the
   release-contract window); `/design`(int) or `/dev`(src) for the
   int-layer trio (site 5). The NC-2 allow-list entries cite this FIXME
   until then.
