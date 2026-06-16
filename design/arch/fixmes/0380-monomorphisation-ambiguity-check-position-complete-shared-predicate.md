---
number: 0380
target: /design
filed_by: /arch
filed_at: 2026-06-16
sprint_filed: 84
refers_to: design/typecheck/monomorphisation.md §4 (The ambiguity check — §4.1 role, §4.2 where it fires, §4.3 error variant), crates/cranelisp-typecheck/src/program.rs §find_ambiguous_let_binding + §is_ambiguous_codegen_reaching_type, design/arch/bounded-contexts.md §3 invariant 9, crates/cranelisp-types/src/types.rs §Type::is_representation_undetermined
status: open
---

# `monomorphisation.md` §4 ambiguity check needs re-grounding: POSITION-COMPLETE scan via the shared `is_representation_undetermined()` predicate (FIXME 0379 belt-and-braces)

## Issue

The S84 Wave-2 user ruling (2026-06-16, "belt-and-braces", FIXME 0379) makes the
§3.11.1 ambiguity check **position-complete** and **predicate-shared** with the
backend RC backstop. `design/typecheck/monomorphisation.md` §4 (re-grounded by FIXME
0376) does not yet reflect this — it frames the ambiguity check as a **root-type-only**
check that fires once per top-level form at finalisation against the form's *finalised
scheme* (§4.2: "At the post-inference generalisation/finalisation boundary of each
top-level form … a var **free at the root** and not quantified"). That framing is
correct for the genuinely-unpinnable-top-level-var residue, but it is **positionally
incomplete** for the soundness obligation 0379 surfaced.

The empirical hole (HEAD `77c634a`, /review repro): a `Mixed`-shaped ADT carrying a
free `Type::Var` (`(Option a)`, `(Box a)`) reaches codegen through a **non-`let`**
value position — a match scrutinee (`(Pure (match (id Non) …))`), a fn-call arg, a vec
element (`(first-tag [(id Non)])`), a ctor field, an if-branch, a ParBind binding — and
is reached-but-not-checked by today's `let`-only scanner (`find_ambiguous_let_binding`,
`program.rs:1522`). The backend `classify(Type::Var)→unreachable!` backstop cannot catch
it either (a `Mixed` ADT routes to `classify_adt` by ctor shape; the free var rides
invisibly in the unused args, never reaching the `Type::Var` arm). So both guards miss
it — exit-0-by-luck-of-shape, one data-ctor-field deref from a `<1024` use-after-free.

## Proposed resolution

Re-ground `monomorphisation.md` §4 so the ambiguity check is:

1. **Position-complete.** It fires the per-node check on the resolved type at **every
   codegen-reaching value position** `for_each_child_expr` already visits — `Expr::Apply.args`,
   `Expr::Match` scrutinee + arm bodies, `Expr::If` branches, `Expr::VecLit` elements,
   `Expr::ConstrADT` fields, `Expr::ParBind` bindings, nested/return positions — NOT only
   `let`-binding values. The recursion was already complete; only the per-node *check*
   was `let`-gated. `find_ambiguous_top_level_form` walks the same generalised scanner.
   (This is in addition to — not a replacement for — the root-type unpinnable-var check
   §4.2 already describes; both are the ambiguity error, surfaced at different sites.)

2. **Predicate-shared, not a local heuristic.** Replace the inline
   `is_ambiguous_codegen_reaching_type` body (`program.rs:1584`, the `Vec`-excluding,
   ADT-arg-free-var heuristic) with a call to the new `cranelisp-types` shared predicate
   **`Type::is_representation_undetermined()`** (`crates/cranelisp-types/src/types.rs`,
   landed S84 Wave 2). It is THE single source of truth shared with the backend RC
   backstop so the two crates agree on the dangerous set by construction (Principle 7 +
   18). The predicate is TRUE for bare `Type::Var`, `Type::TyConApp`, and a non-`Vec`
   `Type::ADT` carrying a free var; FALSE for `Type::Fn`, `(Vec a)`, fully concrete
   types, and a `Type::ADT` with no free var. On the typecheck side the predicate is
   **directly** the ambiguity verdict — under full mono-from-roots a genuinely free var
   in a codegen-reaching position means no root pins it, so the conservative `true` is a
   correct rejection (not a false positive).

3. **Note the relationship to the slot-gate primary.** §4.1 already demotes the check to
   a "secondary backstop" to the structural slot gate — keep that framing; the
   position-completeness is what makes the *secondary* backstop actually total (so a
   non-`let`-position `Mixed`-ADT-with-free-var that the slot gate did not catch upstream
   is rejected here cleanly, before it reaches the backend's own position-complete
   backstop). Record the three-layer belt-and-braces (slot gate primary → typecheck
   position-complete check → backend RC backstop, all sharing the predicate) consistent
   with BC §3 invariant 9.

## Operational implication / Context

- This is /design(typecheck)'s to action in its own doc (`monomorphisation.md`); /arch
  does not edit per-crate design docs. The /dev(typecheck) implementation of the
  position-complete check is the FIXME-0379 typecheck seam (which stays OPEN for the
  /dev relay to close); this FIXME ensures the per-crate design doc grounds it before
  /dev implements, per the same discipline FIXME 0376 followed for the slot gate.
- A small note appended to §4 may suffice if the existing §4.2 root-check prose is kept
  and a §4.4 (or §4.2 addendum) adds the position-complete value-position scan + the
  shared-predicate substitution. /arch's read is that this is a *material* enough
  framing change (root-only → position-complete) to warrant the design-doc grounding,
  not just an inline code comment — hence this FIXME rather than a silent expectation.
- The shared predicate + both consumption seams are specified at FIXME 0379 (arch-design-
  complete, left open) and BC §3 invariant 9. The backend half (`design/backend/ring2-rc.md`
  §1.6) is /design(backend)'s parallel grounding for the WIDENED 0375 backstop.
