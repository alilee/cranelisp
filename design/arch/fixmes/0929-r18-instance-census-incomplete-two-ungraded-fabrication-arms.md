---
number: 0929
target: /arch
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

1. Extend R18's instance list with sites 1 and 2 (or rule either legitimate,
   with the proof cited on the row).
2. Name the two model sites on the row.
3. Answer the structural-closure question; if census-as-enforcement is
   accepted, record the residual grade on the row.
4. Route the two arms' dispositions to their owners (`/design`/`/dev`
   typecheck for fixpoint.rs; `/design`/`/dev` backend for drop_glue.rs) —
   the NC-2 allow-list entries cite this FIXME until then.
