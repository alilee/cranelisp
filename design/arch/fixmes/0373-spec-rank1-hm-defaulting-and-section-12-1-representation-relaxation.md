---
number: 0373
target: /spec
filed_by: /arch
filed_at: 2026-06-16
sprint_filed: 83
refers_to: spec/ §3.x (type system / Hindley–Milner), spec/ §3.6.6 (first-class constrained values), spec/ §12.1 (value representation), design/arch/bounded-contexts.md §3 invariant 9, design/arch/bounded-contexts.md §2 (monomorphisation-from-roots note)
status: open
---

# Spec: state rank-1 HM + monomorphic-recursion explicitly; add a defaulting/ambiguity rule; relax §12.1 representation wording (Tier-2-gated)

## Issue

The 0373 architectural investigation (user-ratified 2026-06-14) settled that Cranelisp is **rank-1 Hindley–Milner** and that full monomorphisation from the program roots is therefore **complete** — the durable architecture conclusion is recorded at `bounded-contexts.md` §3 invariant 9 (backend RC soundness) and §2 (typecheck monomorphisation-from-roots). Three spec-side gaps surfaced during that investigation:

1. **The rank-1 guarantee is implicit, not stated.** The whole fix direction (full monomorphisation, keeping representation backend-internal) rests on the language being rank-1: `Type` has no quantified (`forall`/`Scheme`) variant in value position, every use site instantiates, and monomorphic recursion is enforced (`crates/cranelisp-typecheck/src/program.rs`). §3.6.6 already forbids first-class constrained values, which is the constrained-polymorphism corollary, but the broader rank-1 + monomorphic-recursion guarantee is not stated as a normative property of the type system anywhere a reader can cite.

2. **No defaulting/ambiguity rule for unconstrained top-level type vars.** The spec has NO defaulting rule. An expression whose top-level type retains an unconstrained type variable (no use site pins it to a concrete type) is unrepresentable under full monomorphisation — there is no concrete instance to compile. The spec must say what happens. Recommended: **reject as ambiguous** (a type error at the unresolved-var site), NOT a Haskell-style numeric defaulting. Rejecting keeps representation a backend-internal detail and keeps the "no `Type::Var` reaches codegen" invariant total.

3. **§12.1 over-commits representation.** §12.1 mandates "every value is one machine word". Under full monomorphisation that uniformity stops being load-bearing: with concrete types at every codegen site, the backend can choose each concrete type's representation (`char`/`u16`/`f32`/unboxed-small-ADT) with no language-level or ABI-level change. §12.1 should relax from a uniform-word mandate to a **backend-chooses-representation** statement.

## Proposed resolution

- (i) Add a normative §3.x statement: Cranelisp is rank-1 HM — no quantified types in value position; instantiation at every use; monomorphic recursion enforced. Cross-reference §3.6.6 as the constrained-value corollary.
- (ii) Add a defaulting/ambiguity rule: an unconstrained type variable remaining in a top-level type after inference is a **type error** (ambiguous; no defaulting). State the diagnostic intent.
- (iii) Relax §12.1 representation wording to backend-internal **once Tier 2 lands** (FIXME 0374, /typecheck). Until Tier 2 guarantees concrete types at every codegen site, §12.1's uniform-word statement is still operatively true — **do not relax (iii) ahead of Tier 2.** (i) and (ii) may land independently of Tier 2.

This can be one FIXME with three parts (above) or split per-part — /spec's call.

## Operational implication / Context

Part (iii) is gated on FIXME 0374 (/typecheck, Tier 2 full monomorphisation). Parts (i) and (ii) are independent and could land any sprint. Companion FIXMEs: 0374 (/typecheck — Tier 2) and 0375 (/backend — retire the `<1024` guard from the `Type::Var` path once concreteness is guaranteed). The architecture conclusion these implement is recorded at `bounded-contexts.md` §3 invariant 9 + §2.
